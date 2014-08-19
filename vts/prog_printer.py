import re


class ProgressPrinter:
  def __init__(self):
    self.indent = 0
    self.muted = False
  def p(self, s):
#    if self.muted:
#      return
#    print " " * self.indent + s
    self.pn(s, self.indent)

  def pn(self, s, n):
    if type(s) != str:
      self.pn(str(s), n)
      return
    if self.muted:
      return
    print " " * n + re.sub('\n', '\n' + " " * n, s)

  def inc(self):
    self.indent += 2
  def dec(self):
    self.indent -= 2
  def reset(self):
    self.indent = 0
  def mute(self):
    #self.p = lambda x,y: pass
    self.muted = True

prog = ProgressPrinter()

def pn(s, n):
  prog.pn(s, n)
def p(s):
  prog.p(s)
def inc():
  prog.inc()
def dec():
  prog.dec()
def reset():
  prog.indent = 0

def mute():
  prog.mute()
