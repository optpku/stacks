/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiberSections

variable {X S : Scheme.{u}}

/-- The scheme-theoretic fiber over `s` lies over the inverse image of every open
neighborhood of `s`. -/
theorem preimageTop (f : X ⟶ S) (s : S) (U : S.Opens) (hs : s ∈ U) :
    (f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ := sorry

/-- The neighborhood restriction maps to fiberwise global sections form a compatible family. -/
theorem pushforwardStalkMap_naturality (f : X ⟶ S) (s : S)
    {U V : (OpenNhds s)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion s).op ⋙
          ((TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf).presheaf).map i) ≫
        CommRingCat.ofHom (Scheme.Hom.sectionsMapAlong (f.fiberι s)
          (f ⁻¹ᵁ V.unop.1) ⊤ (preimageTop f s V.unop.1 V.unop.2).symm.le) =
      CommRingCat.ofHom (Scheme.Hom.sectionsMapAlong (f.fiberι s)
        (f ⁻¹ᵁ U.unop.1) ⊤ (preimageTop f s U.unop.1 U.unop.2).symm.le) := sorry

/-- The canonical map from the stalk at `s` of `f_* 𝒪_X` to global sections of the
scheme-theoretic fiber of `f` over `s`. -/
noncomputable def pushforwardStalkMap (f : X ⟶ S) (s : S) :
    (((TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf).presheaf.stalk s) →+*
      Scheme.globalSectionsRing (f.fiber s) :=
  (colimit.desc _
    { pt := Scheme.globalSectionsRing (f.fiber s)
      ι :=
        { app := fun U ↦ CommRingCat.ofHom <| Scheme.Hom.sectionsMapAlong (f.fiberι s)
            (f ⁻¹ᵁ U.unop.1) ⊤ (preimageTop f s U.unop.1 U.unop.2).symm.le
          naturality := fun _ _ i ↦ pushforwardStalkMap_naturality f s i } }).hom

/-- On a germ represented over a neighborhood `U` of `s`, `pushforwardStalkMap` is restriction
along `f.fiberι s` to global sections of the fiber. -/
theorem pushforwardStalkMap_germ (f : X ⟶ S) (s : S) (U : S.Opens)
    (hs : s ∈ U) (a : Γ(X, f ⁻¹ᵁ U)) :
    pushforwardStalkMap f s
        (((TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf).presheaf.germ U s hs a) =
      Scheme.Hom.sectionsMapAlong (f.fiberι s) (f ⁻¹ᵁ U) ⊤
        (preimageTop f s U hs).symm.le a := sorry

end AlgebraicGeometry.Scheme.Hom.FiberSections

end
