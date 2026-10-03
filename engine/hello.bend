# hello.bend: toolchain smoke test. `bend engine/hello.bend` should print
# "Hello, world!"; if it doesn't, Bend is not installed correctly.
import Base

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("Hello, world!")
