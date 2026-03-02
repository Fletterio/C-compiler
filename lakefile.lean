import Lake
open Lake DSL

package «c-compiler»

lean_lib «Lexer»
lean_lib «Driver»

lean_exe «c-compiler» where
  root := `Driver.Main
