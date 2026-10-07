module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Global sections of sheaves on topological spaces

Re-exports and specializes `Mathlib.CategoryTheory.Sites.GlobalSections` to the opens topology.
The global sections functor `Γ` sends a sheaf `F` on `X` to `F(X) = F.presheaf.obj (op ⊤)`.

Used by 16+ downstream files across Chap06/07/20/21.
-/
