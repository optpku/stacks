module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResolutionProperty.Limit
import StacksCheckRecall

/-!
# Resolution property of directed affine limits of algebraic spaces

A specified inverse limit of quasi-compact, absolutely quasi-separated algebraic
spaces over a scheme with affine transition morphisms has the resolution property
if and only if some stage does.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 76.56.5: a specified inverse limit of quasi-compact and quasi-separated
algebraic spaces over a scheme `S` with affine transition morphisms has the
resolution property if and only if some stage does. -/
@[stacks 0GV2]
#check (AlgebraicGeometry.AlgebraicSpace.Limit.hasResolutionProperty_iff_exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ i, IsQuasiCompact (D.obj i)]
    [∀ i, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))],
    SheafOfModules.HasResolutionProperty (structureSheaf c.pt) ↔
      ∃ i : I, SheafOfModules.HasResolutionProperty (structureSheaf (D.obj i)))
