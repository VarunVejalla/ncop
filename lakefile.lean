import Lake
open Lake DSL

package ncop where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

lean_lib NCop where

lean_lib Candidates where
