import Tests.CBCExternal
import Tests.SemanticHtml

unsafe def main : IO UInt32 := do
  Tests.CBCExternal.check
  Tests.SemanticHtml.check
  IO.println "CBC informalization integration tests passed"
  return 0
