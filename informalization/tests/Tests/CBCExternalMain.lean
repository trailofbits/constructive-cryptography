import Tests.CBCExternal

unsafe def main : IO UInt32 := do
  Tests.CBCExternal.check
  IO.println "CBC external semantic test passed"
  return 0
