/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Cech

/-!
# Composition of local-cohomology functors

Successive right adjoints for support in two finitely generated ideals lift to support in their
supremum and admit a canonical comparison with the right adjoint for that supremum.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/-- Applying a `J`-support right adjoint to an object with `I`-power-torsion cohomology produces
an object with `(I ⊔ J)`-power-torsion cohomology. -/
theorem iterated_mem (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ) (K : IdealPowerTorsion I) :
    cohomologyIn (ModuleCat.isIdealPowerTorsion (I ⊔ J))
      ((IdealPowerTorsion.inclusion I ⋙ RΓJ ⋙
        IdealPowerTorsion.inclusion J).obj K) := sorry

/-- The restriction of `J`-support local cohomology from the `I`-torsion subcategory to the
`(I ⊔ J)`-torsion subcategory. -/
noncomputable def iterated (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ) :
    IdealPowerTorsion I ⥤ IdealPowerTorsion (I ⊔ J) :=
  (cohomologyIn (ModuleCat.isIdealPowerTorsion (I ⊔ J))).lift
    (IdealPowerTorsion.inclusion I ⋙ RΓJ ⋙ IdealPowerTorsion.inclusion J)
    (iterated_mem I J hI hJ RΓJ hRΓJ)

/-- Forgetting the support condition identifies `iterated` with applying `RΓJ` to the
underlying `I`-torsion derived object. -/
theorem iterated_obj (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ) (K : IdealPowerTorsion I) :
    (IdealPowerTorsion.inclusion (I ⊔ J)).obj
        ((iterated I J hI hJ RΓJ hRΓJ).obj K) =
      (IdealPowerTorsion.inclusion J).obj
        (RΓJ.obj ((IdealPowerTorsion.inclusion I).obj K)) := sorry

/-- The component of the canonical comparison from iterated local cohomology to local
cohomology supported on the zero locus of `I ⊔ J`. -/
noncomputable def iteratedToSumApp (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (RΓIJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (I ⊔ J))
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ)
    (hRΓIJ : IdealPowerTorsion.inclusion (I ⊔ J) ⊣ RΓIJ)
    (K : DerivedCategory (ModuleCat A)) :
    (RΓI ⋙ iterated I J hI hJ RΓJ hRΓJ).obj K ⟶ RΓIJ.obj K :=
  hRΓIJ.homEquiv _ _
    (hRΓJ.counit.app ((IdealPowerTorsion.inclusion I).obj (RΓI.obj K)) ≫
      hRΓI.counit.app K)

/-- The components of the comparison from iterated support to support in the ideal supremum
are natural in the derived object. -/
theorem iteratedToSum_naturality (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (RΓIJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (I ⊔ J))
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ)
    (hRΓIJ : IdealPowerTorsion.inclusion (I ⊔ J) ⊣ RΓIJ)
    {K L : DerivedCategory (ModuleCat A)} (f : K ⟶ L) :
    (RΓI ⋙ iterated I J hI hJ RΓJ hRΓJ).map f ≫
        iteratedToSumApp I J hI hJ RΓI RΓJ RΓIJ hRΓI hRΓJ hRΓIJ L =
      iteratedToSumApp I J hI hJ RΓI RΓJ RΓIJ hRΓI hRΓJ hRΓIJ K ≫
        RΓIJ.map f := sorry

/-- The canonical natural comparison from iterated local cohomology to local cohomology
supported on the zero locus of `I ⊔ J`. -/
noncomputable def iteratedToSum (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (RΓIJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (I ⊔ J))
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ)
    (hRΓIJ : IdealPowerTorsion.inclusion (I ⊔ J) ⊣ RΓIJ) :
    RΓI ⋙ iterated I J hI hJ RΓJ hRΓJ ⟶ RΓIJ where
  app := iteratedToSumApp I J hI hJ RΓI RΓJ RΓIJ hRΓI hRΓJ hRΓIJ
  naturality := fun _ _ f ↦
    iteratedToSum_naturality I J hI hJ RΓI RΓJ RΓIJ hRΓI hRΓJ hRΓIJ f

/-- The canonical comparison from iterated local cohomology to local cohomology supported on
the zero locus of the ideal supremum is an isomorphism. -/
theorem iteratedToSum_isIso (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion J)
    (RΓIJ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (I ⊔ J))
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓJ : IdealPowerTorsion.inclusion J ⊣ RΓJ)
    (hRΓIJ : IdealPowerTorsion.inclusion (I ⊔ J) ⊣ RΓIJ) :
    IsIso (iteratedToSum I J hI hJ RΓI RΓJ RΓIJ hRΓI hRΓJ hRΓIJ) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
