


class ProgressPrinter:
  def __init__(self):
    self.indent = 0
  def p(self, s):
    if mute:
      return
    print " " * self.indent + s
  def inc(self):
    self.indent += 2
  def dec(self):
    self.indent -= 2
  def reset(self):
    self.indent = 0
  def mute(self):
    #self.p = lambda x,y: pass
    self.mute = True

prog = ProgressPrinter()

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