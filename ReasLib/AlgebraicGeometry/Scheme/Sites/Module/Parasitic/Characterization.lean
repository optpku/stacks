/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Adjunction

/-!
# Characterizations of parasitic adequate module sheaves
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules.Adeq

/-- A parasitic adequate module sheaf has equivalent vanishing, parasitic, and
  affine-cover formulations. -/
theorem parasitic_tfae (S : Scheme.{u}) (τ : StandardTopology)
    (F : SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
      (@SheafOfModules.affineEvaluationUnderlying S τ)) :
    let ℱ := F.obj.val
    List.TFAE [
      IsZero ((zariskiRestriction S τ).obj F),
      SheafOfModules.IsParasiticOne F.obj,
      PresheafOfModules.IsParasitic ℱ τ,
      ∀ U : S.Opens, IsZero (ℱ.obj (op (Over.mk U.ι))),
      ∃ 𝒰 : S.AffineOpenCover, ∀ i : 𝒰.I₀,
        IsZero (ℱ.obj (op (Over.mk (𝒰.f i))))] := sorry

end SheafOfModules.Adeq
