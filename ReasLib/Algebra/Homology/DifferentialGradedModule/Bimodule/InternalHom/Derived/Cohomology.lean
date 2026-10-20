module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Naturality
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Hom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.KInjective
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.Resolution

/-!
# Cohomology of differential graded bimodule internal Hom

The cohomology of `internalHom T I` first represents shifted morphisms in the intrinsic DG
homotopy category. When `I` is K-injective, localization and a quasi-isomorphism `M ⟶ I`
identify those morphisms with shifted morphisms from `T.toRightModule` to `M` in the derived
category. The construction is natural in both the bimodule source and the resolved target.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedBimodule.InternalHom.Cohomology

variable {R : Type u} [CommRing R]

section General

variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- The underlying cochain complex of bimodule internal Hom is the enriched Hom complex of the
underlying right `B`-module. -/
@[stacks 09LG "cochain comparison for the fixed-source internal Hom"]
def cochainIso (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    (P : DifferentialGradedModule.{u, v} B) :
    (DifferentialGradedBimodule.internalHom T P).toCochainComplex ≅
      DifferentialGradedCategory.homComplex T.toRightModule P :=
  Iso.refl _

/-- The cochain comparison induces the canonical isomorphism on degree-`n` homology. -/
@[stacks 09LG "homology comparison for the fixed-source internal Hom"]
noncomputable def homologyIso (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    (P : DifferentialGradedModule.{u, v} B) (n : ℤ) :
    (DifferentialGradedBimodule.internalHom T P).homology n ≅
      (DifferentialGradedCategory.homComplex T.toRightModule P).homology n :=
  HomologicalComplex.homologyMapIso (cochainIso T P) n

/-- The map on internal-Hom cohomology induced contravariantly by a bimodule morphism. -/
@[stacks 09LG "source map on fixed-source internal-Hom cohomology"]
noncomputable def sourceMap
    {T T' : DifferentialGradedBimodule.{u, v, w, x} A B} (f : T ⟶ T')
    (P : DifferentialGradedModule.{u, v} B) (n : ℤ) :
    (DifferentialGradedBimodule.internalHom T' P).homology n ⟶
      (DifferentialGradedBimodule.internalHom T P).homology n :=
  HomologicalComplex.homologyMap
    (DifferentialGradedModule.Hom.toCochainMap
      (DifferentialGradedBimodule.InternalHom.precomp f P)) n

/-- The map on fixed-source internal-Hom cohomology induced covariantly by a target morphism. -/
@[stacks 09LG "target map on fixed-source internal-Hom cohomology"]
noncomputable def targetMap
    (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    {P Q : DifferentialGradedModule.{u, v} B} (g : P ⟶ Q) (n : ℤ) :
    (DifferentialGradedBimodule.internalHom T P).homology n ⟶
      (DifferentialGradedBimodule.internalHom T Q).homology n :=
  HomologicalComplex.homologyMap
    (DifferentialGradedModule.Hom.toCochainMap
      (DifferentialGradedBimodule.InternalHom.postcomp T g)) n

end General

variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, v} R}

-- The comparison owners below require the DG-algebra and module carriers in the same universe.

/-- Internal-Hom cohomology represents shifted morphisms of underlying right `B`-modules in
the intrinsic DG homotopy category. -/
@[stacks 09K4 "bimodule internal-Hom cohomology as shifted homotopy Hom"]
noncomputable def homotopyLinearEquiv
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    (P : DifferentialGradedModule.{u, v} B) (n : ℤ) :
    (DifferentialGradedBimodule.internalHom T P).homology n ≃ₗ[R]
      ((DifferentialGradedModule.toK B).obj T.toRightModule ⟶
        (DifferentialGradedModule.toK B).obj P[n]) :=
  (homologyIso T P n).toLinearEquiv.trans
    (DifferentialGradedModule.Homotopy.shiftHomotopyLinearEquivHomology
      T.toRightModule P n).symm

-- The remaining comparisons additionally inherit this boundary through derived shifts,
-- K-injectivity, and property-I resolutions.

/-- The homotopy representation of internal-Hom cohomology is contravariantly natural in the
bimodule source, through the explicit precomposition map of internal Hom. -/
@[stacks 09K4 "source naturality of shifted homotopy Hom"]
theorem homotopyLinearEquiv_naturality_source
    {T T' : DifferentialGradedBimodule.{u, v, w, v} A B} (f : T ⟶ T')
    (P : DifferentialGradedModule.{u, v} B) (n : ℤ)
    (x : (DifferentialGradedBimodule.internalHom T' P).homology n) :
    homotopyLinearEquiv T P n (sourceMap f P n x) =
      (DifferentialGradedModule.toK B).map
          (DifferentialGradedBimodule.Hom.toRightHom f) ≫
        homotopyLinearEquiv T' P n x := sorry

/-- The homotopy representation of internal-Hom cohomology is covariantly natural in the
target right DG module. -/
@[stacks 09K4 "target naturality of shifted homotopy Hom"]
theorem homotopyLinearEquiv_naturality_target
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {P Q : DifferentialGradedModule.{u, v} B} (g : P ⟶ Q) (n : ℤ)
    (x : (DifferentialGradedBimodule.internalHom T P).homology n) :
    homotopyLinearEquiv T Q n (targetMap T g n x) =
      homotopyLinearEquiv T P n x ≫
        (DifferentialGradedModule.toK B).map
          (DifferentialGradedModule.shiftMap g n) := sorry

/-- A quasi-isomorphism `M ⟶ I` identifies the derived image of the explicit shift `I[n]`
with the shift of the derived image of `M`. -/
@[stacks 0CS5 "shift comparison along a K-injective replacement"]
noncomputable def resolutionShiftIso
    (M I : DifferentialGradedModule.{u, v} B) (i : M ⟶ I)
    (hi : DifferentialGradedModule.quasiIso B
      ((DifferentialGradedModule.toK B).map i)) (n : ℤ) :
    (DifferentialGradedModule.Derived.Q B).obj
        ((DifferentialGradedModule.toK B).obj I[n]) ≅
      ((DifferentialGradedModule.Derived.Q B).obj
        ((DifferentialGradedModule.toK B).obj M))⟦n⟧ :=
  DifferentialGradedModule.Derived.toKShiftIso I n ≪≫
    (shiftFunctor (DifferentialGradedModule.Derived.Category B) n).mapIso
      (DifferentialGradedModule.Derived.isoOfQuasiIso
        ((DifferentialGradedModule.toK B).map i) hi).symm

/-- For a specified K-injective quasi-isomorphic target, internal-Hom cohomology is the
`R`-module of shifted derived morphisms from the underlying right module of the bimodule. -/
@[stacks 0CS5 "derived internal-Hom cohomology from a K-injective model"]
noncomputable def derivedLinearEquiv
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    (M I : DifferentialGradedModule.{u, v} B) (i : M ⟶ I)
    (hi : DifferentialGradedModule.quasiIso B
      ((DifferentialGradedModule.toK B).map i))
    (hI : DifferentialGradedModule.Homotopy.kInjective B
      ((DifferentialGradedModule.toK B).obj I)) (n : ℤ) :
    (DifferentialGradedBimodule.internalHom T I).homology n ≃ₗ[R]
      ((DifferentialGradedModule.Derived.Q B).obj
          ((DifferentialGradedModule.toK B).obj T.toRightModule) ⟶
        ((DifferentialGradedModule.Derived.Q B).obj
          ((DifferentialGradedModule.toK B).obj M))⟦n⟧) :=
  (homotopyLinearEquiv T I n).trans
    ((DifferentialGradedModule.Homotopy.KInjective.homLinearEquiv
        ((DifferentialGradedModule.toK B).obj T.toRightModule)
        ((DifferentialGradedModule.toK B).obj I[n])
        (DifferentialGradedModule.Homotopy.KInjective.toK_shift I hI n)).trans
      (CategoryTheory.Linear.homCongr R (Iso.refl _)
        (resolutionShiftIso M I i hi n)))

/-- The explicit derived equivalence localizes the represented homotopy morphism and then uses
the chosen resolution comparison on the shifted target. -/
@[simp, stacks 0CS5 "formula for the K-injective derived cohomology comparison"]
theorem derivedLinearEquiv_apply
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    (M I : DifferentialGradedModule.{u, v} B) (i : M ⟶ I)
    (hi : DifferentialGradedModule.quasiIso B
      ((DifferentialGradedModule.toK B).map i))
    (hI : DifferentialGradedModule.Homotopy.kInjective B
      ((DifferentialGradedModule.toK B).obj I)) (n : ℤ)
    (x : (DifferentialGradedBimodule.internalHom T I).homology n) :
    derivedLinearEquiv T M I i hi hI n x =
      (DifferentialGradedModule.Derived.Q B).map
          (homotopyLinearEquiv T I n x) ≫
        (resolutionShiftIso M I i hi n).hom := sorry

/-- Lemma 22.31.4 (0CS5): a property-I resolution computes internal-Hom cohomology as shifted
morphisms in the derived category of right DG `B`-modules. -/
@[stacks 0CS5 "bimodule internal-Hom cohomology as derived shifted Hom"]
noncomputable def resolutionLinearEquiv
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ) :
    (DifferentialGradedBimodule.internalHom T I.obj).homology n ≃ₗ[R]
      ((DifferentialGradedModule.Derived.Q B).obj
          ((DifferentialGradedModule.toK B).obj T.toRightModule) ⟶
        ((DifferentialGradedModule.Derived.Q B).obj
          ((DifferentialGradedModule.toK B).obj M))⟦n⟧) :=
  derivedLinearEquiv T M I.obj I.ι I.quasiIso_ι
    (DifferentialGradedModule.HasPropertyI.kInjective
      (DifferentialGradedModule.PropertyI.Resolution.propertyI_obj B I)) n

/-- The property-(I) resolution equivalence evaluates by localizing the represented homotopy
morphism and transporting along the shifted resolution comparison. -/
@[stacks 0CS5 "property-I resolution cohomology comparison formula", simp]
theorem resolutionLinearEquiv_apply
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ)
    (x : (DifferentialGradedBimodule.internalHom T I.obj).homology n) :
    resolutionLinearEquiv T I n x =
      (DifferentialGradedModule.Derived.Q B).map
          (homotopyLinearEquiv T I.obj n x) ≫
        (resolutionShiftIso M I.obj I.ι I.quasiIso_ι n).hom := sorry

/-- The derived internal-Hom cohomology equivalence is contravariantly natural in the bimodule
source via the precomposition map from Lemma 22.31.3. -/
@[stacks 0CS5 "source naturality of the K-injective derived cohomology comparison"]
theorem derivedLinearEquiv_naturality_source
    {T T' : DifferentialGradedBimodule.{u, v, w, v} A B} (f : T ⟶ T')
    (M I : DifferentialGradedModule.{u, v} B) (i : M ⟶ I)
    (hi : DifferentialGradedModule.quasiIso B
      ((DifferentialGradedModule.toK B).map i))
    (hI : DifferentialGradedModule.Homotopy.kInjective B
      ((DifferentialGradedModule.toK B).obj I)) (n : ℤ)
    (x : (DifferentialGradedBimodule.internalHom T' I).homology n) :
    derivedLinearEquiv T M I i hi hI n (sourceMap f I n x) =
      (DifferentialGradedModule.Derived.Q B).map
          ((DifferentialGradedModule.toK B).map
            (DifferentialGradedBimodule.Hom.toRightHom f)) ≫
        derivedLinearEquiv T' M I i hi hI n x := sorry

/-- The derived internal-Hom cohomology equivalence is covariantly natural in compatible maps
of resolved targets. -/
@[stacks 0CS5 "target naturality of the K-injective derived cohomology comparison"]
theorem derivedLinearEquiv_naturality_target
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M M' I I' : DifferentialGradedModule.{u, v} B}
    (i : M ⟶ I) (i' : M' ⟶ I')
    (hi : DifferentialGradedModule.quasiIso B
      ((DifferentialGradedModule.toK B).map i))
    (hi' : DifferentialGradedModule.quasiIso B
      ((DifferentialGradedModule.toK B).map i'))
    (hI : DifferentialGradedModule.Homotopy.kInjective B
      ((DifferentialGradedModule.toK B).obj I))
    (hI' : DifferentialGradedModule.Homotopy.kInjective B
      ((DifferentialGradedModule.toK B).obj I'))
    (f : M ⟶ M') (g : I ⟶ I') (comm : i ≫ g = f ≫ i') (n : ℤ)
    (x : (DifferentialGradedBimodule.internalHom T I).homology n) :
    derivedLinearEquiv T M' I' i' hi' hI' n (targetMap T g n x) =
      derivedLinearEquiv T M I i hi hI n x ≫
        ((DifferentialGradedModule.Derived.Q B).map
          ((DifferentialGradedModule.toK B).map f))⟦n⟧' := sorry

end DifferentialGradedBimodule.InternalHom.Cohomology
