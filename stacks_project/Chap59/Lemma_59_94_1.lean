/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.VanishingCycles.Cospecialization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.EtaleVanishingCycles
open DerivedCategory.TStructure

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleVanishingCycles

variable {X S : Scheme.{u}} (f : X ⟶ S) (sbar : GeometricPoint S)
variable (Rsh : Type u) [CommRing Rsh]
variable [Algebra (S.presheaf.stalk sbar.image) Rsh]
variable [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]

/-- The geometric closed-fibre comparison into the henselized fibre. -/
abbrev cospecializationI
    (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar Rsh)
    (hiS : iS ≫ strictHenselizationMap S sbar Rsh = sbar.hom) :
    pullback f sbar.hom ⟶ henselizedFiber f sbar Rsh :=
  geometricFiberToHenselized f sbar Rsh iS hiS

/-- Étale direct image on abelian sheaves. -/
abbrev directImage {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    Coefficients Y ⥤ Coefficients Z :=
  Etale.Abelian.directImage g

end AlgebraicGeometry.Scheme.EtaleVanishingCycles

/- Lemma 59.94.1: for bounded-below coefficients relative to which `f` is locally
acyclic, the inverse image of the concrete cospecialization comparison is an isomorphism. -/
@[stacks 0GJU] #check (AlgebraicGeometry.Scheme.isIso_inverseImage_etaleCohomologyBeta :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (sbar : GeometricPoint S)
    (Rsh : Type u) [CommRing Rsh]
    [Algebra (S.presheaf.stalk sbar.image) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]
    (tbar : GeometricPoint (strictHenselizationScheme S sbar Rsh))
    (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar Rsh)
    (hiS : iS ≫ strictHenselizationMap S sbar Rsh = sbar.hom)
    (K : Complexes X) (hK : t.plus K) [LocallyAcyclicRelative f K],
    IsIso ((derivedInverseImage (geometricFiberToHenselized f sbar Rsh iS hiS)).map
      (etaleCohomologyBeta f sbar Rsh tbar K)))
