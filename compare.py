#!/usr/bin/python3

import subprocess
from subprocess import STDOUT, PIPE, check_output
import os
import re
import sys
import time

z3   = ["z3", "-T:0.1"]
smtx = ["./.stack-work/dist/x86_64-linux-tinfo6/Cabal-3.0.1.0/build/smtx/smtx", "-v", "0", "-r", "4242"]
commands = {"z3":z3, "smtx":smtx}
captions = {"z3":"z3", "smtx":"smtx"}

# https://www.ostricher.com/2015/01/python-subprocess-with-timeout/

RED       = '\033[031m'
GREEN     = '\033[032m'
NORMAL    = '\033[0m'
BOLD      = '\033[1m'
HIGHLIGHT = "\033[043m"

timeout = 12

# TODO why does it fail to highlight discrepancies now!?!?!?

# TODO: better do an xml report and convert to colored output in a second stage.
# also: why not do the comparison in haskell? not many libraries required, less clumsy
# and provide "live updates"?

def do_main():
    # for root, dirs, files in os.walk("resources/QF_UF/QG-classification/loops6/", topdown = False):
    for root, dirs, files in os.walk("resources", topdown = True):

        for name in files:
            if not re.match("^.*smt2$", name):
                continue
#            if not re.match("^.*cnf$", name):
#                continue
            if re.match("^.*gz$", name):
                continue
            if re.match("^.*\\.txt$", name):
                continue

            print( BOLD + os.path.join(root, name) + NORMAL , flush=True )

            # TODO highlight where we beat Z3 (not yet)

            res = {}
            # skip = True
            skip = False

            filo = open(os.path.join(root, name), "r")

            for line in filo:
                if re.search(r'declare-fun.*U.*Bool', line): # hope it is in one line
                    print ("attention, at least one bool-valued function detected: " + line[:-1])
                    # skip = False
                    break

            filo.close()

            if skip:
                continue

            for cmd in ["z3", "smtx"]:
                t1 = time.time()
                proc = subprocess.Popen(['timeout', '{}'.format(timeout)] + commands[cmd] + [os.path.join(root,name)], stdout=PIPE, stderr=PIPE)
                k = proc.wait()
                lines = proc.stdout.readlines()
                t2 = time.time()
                if len(lines) == 0:
                    line = ""
                else:
#                   line = lines[-1][:-1].decode('latin1')
                    line = lines[0][:-1].decode('latin1')
                res[cmd] = (k, line, t2 - t1)
            
            for cmd in ["z3", "smtx"]:

                (k, line, dt) = res[cmd]

                if k != 0:
                    x = ""
                    if res["z3"] == res["smtx"]:
                        x = BOLD
                    print ("- {: <4}: {}{: <6}{} [{}s]" .format (captions[cmd], x, "fail", NORMAL, round(dt, 6)), flush=True)

                else:
                    result = "?"
                    x = ""

                    if res["z3"] == "sat" and res["smtx"] == "unsat":
                        x += HIGHLIGHT
                    if res["z3"] == "unsat" and res["smtx"] == "sat":
                        x += HIGHLIGHT
                    if res["z3"] == res["smtx"]:
                        x += BOLD
                        
                    if line == "unsat":
                        x += RED
                    elif line == "sat":
                        x += GREEN
                    print ("- {: <4}: {}{: <6}{} [{}s]" .format (captions[cmd],  x, line, NORMAL, round(dt, 6)), flush=True)

if __name__=='__main__':
    do_main()

