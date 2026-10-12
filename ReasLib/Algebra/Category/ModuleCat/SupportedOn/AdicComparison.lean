/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.IdealPower.Quotient.Sequential
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Sequential

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A]

/-- The supported-cohomology comparison induced by the canonical exact quotient map. -/
noncomputable def adicComparison
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A)
    (i : ℤ) (n : ℕ) :
    cohomology T (ModuleCat.single0Functor.obj M) i ⟶
      cohomology T
        (ModuleCat.single0Functor.obj ((Ideal.PowerQuotient.system I M).obj (op n))) i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
    ((derivedInclusion T).map
      ((derivedSections T).map
        (ModuleCat.single0Functor.map
          (ModuleCat.ofHom
            (Submodule.mkQ (I ^ n • (⊤ : Submodule A (M : Type u))))))))

/-- The supported-cohomology tower obtained from the exact ideal-power quotient system. -/
noncomputable abbrev adicTower
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A) (i : ℤ) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  supportedCohomologyTower T (Ideal.PowerQuotient.system I M) i

/-- The support comparison on an exact adic quotient points from `V(a)` to `V(J)`. -/
noncomputable def adicQuotientSupportMap
    (I a J : Ideal A) (hJ : J ≤ a) (M : ModuleCat.{u} A) (i : ℤ) (n : ℕ) :
    cohomology (PrimeSpectrum.zeroLocus (a : Set A))
        (ModuleCat.single0Functor.obj ((Ideal.PowerQuotient.system I M).obj (op n))) i ⟶
      cohomology (PrimeSpectrum.zeroLocus (J : Set A))
        (ModuleCat.single0Functor.obj ((Ideal.PowerQuotient.system I M).obj (op n))) i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
    (derivedSupportMap (PrimeSpectrum.zeroLocus_anti_mono_ideal hJ)
      (ModuleCat.single0Functor.obj ((Ideal.PowerQuotient.system I M).obj (op n))))

/-- The quotient support comparison is invertible when the two supports agree on `V(I)`. -/
theorem adicQuotientSupportMap_isIso
    [IsNoetherianRing A] (I a J : Ideal A) (hJ : J ≤ a)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (M : ModuleCat.{u} A) (i : ℤ) (n : ℕ) :
    IsIso (adicQuotientSupportMap I a J hJ M i n) := sorry

/-- The quotientwise supported comparison uses the inverse support map on each adic stage. -/
noncomputable def adicSupportComparison
    [IsNoetherianRing A] (I a J : Ideal A) (hJ : J ≤ a)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (M : ModuleCat.{u} A) (i : ℤ) (n : ℕ) :
    cohomology (PrimeSpectrum.zeroLocus (J : Set A))
        (ModuleCat.single0Functor.obj M) i ⟶
      cohomology (PrimeSpectrum.zeroLocus (a : Set A))
        (ModuleCat.single0Functor.obj ((Ideal.PowerQuotient.system I M).obj (op n))) i :=
  adicComparison (PrimeSpectrum.zeroLocus (J : Set A)) I M i n ≫
    @CategoryTheory.inv _ _ _ _
      (adicQuotientSupportMap I a J hJ M i n)
      (adicQuotientSupportMap_isIso I a J hJ hV M i n)

/-- The quotientwise supported comparisons form a cone over the adic quotient tower. -/
noncomputable def adicSupportComparisonCone
    [IsNoetherianRing A] (I a J : Ideal A) (hJ : J ≤ a)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (M : ModuleCat.{u} A) (i : ℤ) :
    Cone (adicTower (PrimeSpectrum.zeroLocus (a : Set A)) I M i) where
  pt := cohomology (PrimeSpectrum.zeroLocus (J : Set A))
    (ModuleCat.single0Functor.obj M) i
  π :=
    { app := fun n ↦ adicSupportComparison I a J hJ hV M i n.unop
      naturality := sorry }

/-- The canonical map from supported cohomology to the adic quotient limit. -/
noncomputable def adicSupportLimitComparison
    [IsNoetherianRing A] (I a J : Ideal A) (hJ : J ≤ a)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (M : ModuleCat.{u} A) (i : ℤ) :
    cohomology (PrimeSpectrum.zeroLocus (J : Set A))
        (ModuleCat.single0Functor.obj M) i ⟶
      limit (adicTower (PrimeSpectrum.zeroLocus (a : Set A)) I M i) :=
  limit.lift _ (adicSupportComparisonCone I a J hJ hV M i)

/-- The canonical quotientwise formula for the supported limit comparison. -/
theorem adicSupportLimitComparison_π
    [IsNoetherianRing A] (I a J : Ideal A) (hJ : J ≤ a)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (M : ModuleCat.{u} A) (i : ℤ) (n : ℕ) :
    adicSupportLimitComparison I a J hJ hV M i ≫
        limit.π (adicTower (PrimeSpectrum.zeroLocus (a : Set A)) I M i) (op n) =
      adicSupportComparison I a J hJ hV M i n := sorry

/-- The supported-cohomology comparison induced by the quotient of two adic stages. -/
noncomputable def adicTailComparison
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A)
    (m : ℕ) (i : ℤ) (n : ℕ) :
    cohomology T
        (ModuleCat.single0Functor.obj (Ideal.PowerSubmodule.stageObj I M m)) i ⟶
      cohomology T
        (ModuleCat.single0Functor.obj
          ((Ideal.PowerSubmodule.quotientSystem I M m).obj (op n))) i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
    ((derivedInclusion T).map
      ((derivedSections T).map
        (ModuleCat.single0Functor.map
          (Ideal.PowerSubmodule.quotientMap I M m n))))

/-- The supported-cohomology tower of fixed-numerator adic quotients. -/
noncomputable abbrev adicTailTower
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A)
    (m : ℕ) (i : ℤ) : SequentialInverseSystem (ModuleCat.{u} A) :=
  supportedCohomologyTower T (Ideal.PowerSubmodule.quotientSystem I M m) i

/-- The cone of supported-cohomology comparisons for the exact quotient tower. -/
noncomputable def adicComparisonCone
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A)
    (i : ℤ) : Cone (adicTower T I M i) where
  pt := cohomology T (ModuleCat.single0Functor.obj M) i
  π :=
    { app := fun n ↦ adicComparison T I M i n.unop
      naturality := sorry }

/-- The canonical map from supported cohomology to the limit of the exact quotient tower. -/
noncomputable def adicLimitComparison
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A)
    (i : ℤ) :
    cohomology T (ModuleCat.single0Functor.obj M) i ⟶ limit (adicTower T I M i) :=
  limit.lift _ (adicComparisonCone T I M i)

/-- The projection formula for the exact quotient limit comparison. -/
theorem adicLimitComparison_π
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A)
    (i : ℤ) (n : ℕ) :
    adicLimitComparison T I M i ≫ limit.π (adicTower T I M i) (op n) =
      adicComparison T I M i n := sorry

/-- The cone of supported-cohomology comparisons for a fixed-numerator quotient tower. -/
noncomputable def adicTailComparisonCone
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A)
    (m : ℕ) (i : ℤ) : Cone (adicTailTower T I M m i) where
  pt := cohomology T
      (ModuleCat.single0Functor.obj (Ideal.PowerSubmodule.stageObj I M m)) i
  π :=
    { app := fun n ↦ adicTailComparison T I M m i n.unop
      naturality := sorry }

/-- The canonical map from supported cohomology of an adic stage to its quotient limit. -/
noncomputable def adicTailLimitComparison
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A)
    (m : ℕ) (i : ℤ) :
    cohomology T
        (ModuleCat.single0Functor.obj (Ideal.PowerSubmodule.stageObj I M m)) i ⟶
      limit (adicTailTower T I M m i) :=
  limit.lift _ (adicTailComparisonCone T I M m i)

/-- The projection formula for a fixed-numerator quotient limit comparison. -/
theorem adicTailLimitComparison_π
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A)
    (m : ℕ) (i : ℤ) (n : ℕ) :
    adicTailLimitComparison T I M m i ≫
        limit.π (adicTailTower T I M m i) (op n) =
      adicTailComparison T I M m i n := sorry

end CategoryTheory.ModuleCat.SupportedOn
