/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite

/-!
# Representability of locally quasi-finite maps from affine formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A map of presheaves from an affine formal algebraic space is representable
by schemes if it is representable by algebraic spaces and all its scheme base
changes are locally of finite type and chartwise locally quasi-finite. The
presentation hypothesis supplies the size condition by requiring fppf-locally
surjective maps from representables to the source and its relation presheaf.
Local finite type together with chartwise local quasi-finiteness expresses the
locally quasi-finite convention requiring local finite type. -/
theorem relativelyRepresentable_of_locallyQuasiFinite
    {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) [IsAffine X]
    (h_presentation :
      ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ)
    (hf : representableByAlgebraicSpaces f)
    (h_locallyOfFiniteType :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y), AlgebraicSpace.LocallyOfFiniteType (hf.pullbackHom ξ))
    (h_locallyQuasiFinite :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y), AlgebraicSpace.LocallyQuasiFinite (hf.pullbackHom ξ)) :
    yoneda.relativelyRepresentable f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
