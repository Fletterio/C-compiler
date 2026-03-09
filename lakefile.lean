import Lake
open Lake DSL

package «c-compiler»

lean_lib «Lexer»
lean_lib «AST»
lean_lib «Parser»
lean_lib «Semantics»
lean_lib «Tacky»
lean_lib «AssemblyAST»
lean_lib «Emission»
lean_lib «Driver»

lean_exe «c-compiler» where
  root := `Driver.Main
