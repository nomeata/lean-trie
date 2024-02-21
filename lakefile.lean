import Lake
open Lake DSL

package «trie» where
  -- add package configuration options here

lean_lib «Trie» where
  -- add library configuration options here

@[default_target]
lean_exe «trie» where
  root := `Main
