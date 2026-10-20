module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Homology

/-!
# Short-complex homology under change of scalars

This file specializes the generic homology-preservation API to short complexes of modules.
Restriction of scalars is always exact; extension of scalars is exact along a flat ring map.
@stack 063Q
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

namespace ExtendScalars

namespace HomologyComparison

/-- The concrete cokernel presentation of the outgoing differential of a short complex of
modules. -/
@[stacks 063Q "outgoing cokernel presentation for a short complex"]
abbrev outgoingCokernel (K : ShortComplex (ModuleCat R)) :=
  K.X₃ ⧸ LinearMap.range K.g.hom

/-- Applying extension of scalars to the inclusion of cycles still lands in the cycles of the
mapped short complex. -/
theorem cycles_condition (f : R →+* S) (K : ShortComplex (ModuleCat R)) :
    (ModuleCat.extendScalars f).map K.iCycles ≫
        (K.map (ModuleCat.extendScalars f)).g = 0 := sorry

/-- The canonical map from scalar extension of the cycles of a short complex to the concrete
kernel presentation of cycles in the scalar-extended short complex. -/
noncomputable def cycles (f : R →+* S) (K : ShortComplex (ModuleCat R)) :
    (ModuleCat.extendScalars f).obj K.cycles ⟶
      (K.map (ModuleCat.extendScalars f)).moduleCatLeftHomologyData.K :=
  (K.map (ModuleCat.extendScalars f)).moduleCatLeftHomologyData.liftK
    ((ModuleCat.extendScalars f).map K.iCycles) (cycles_condition f K)

/-- Scalar-extended cycles mapped to their homology classes in the scalar-extended short
complex. -/
noncomputable def cycleClass (f : R →+* S) (K : ShortComplex (ModuleCat R)) :
    (ModuleCat.extendScalars f).obj K.cycles ⟶
      (K.map (ModuleCat.extendScalars f)).homology :=
  cycles f K ≫
    (K.map (ModuleCat.extendScalars f)).moduleCatLeftHomologyData.π ≫
      (K.map (ModuleCat.extendScalars f)).moduleCatHomologyIso.inv

/-- The map on scalar-extended cycles kills the scalar extension of every boundary. -/
theorem map_condition (f : R →+* S) (K : ShortComplex (ModuleCat R)) :
    (ModuleCat.extendScalars f).map K.toCycles ≫ cycleClass f K = 0 := sorry

/-- The canonical comparison from scalar extension of short-complex homology to the homology of
the scalar-extended short complex.  This map exists without a flatness hypothesis because
extension of scalars preserves cokernels. -/
noncomputable def map (f : R →+* S) (K : ShortComplex (ModuleCat R)) :
    (ModuleCat.extendScalars f).obj K.homology ⟶
      (K.map (ModuleCat.extendScalars f)).homology :=
  (CokernelCofork.mapIsColimit
      (CokernelCofork.ofπ K.homologyπ K.toCycles_comp_homologyπ)
      K.homologyIsCokernel (ModuleCat.extendScalars f)).desc
    (CokernelCofork.ofπ
      (cycleClass f K) (map_condition f K))

/-- The homology comparison is characterized by its value on scalar-extended cycle classes. -/
theorem fac (f : R →+* S) (K : ShortComplex (ModuleCat R)) :
    (ModuleCat.extendScalars f).map K.homologyπ ≫ map f K =
      cycleClass f K := sorry

/-- The homology comparison is natural in morphisms of short complexes. -/
theorem naturality (f : R →+* S) {K L : ShortComplex (ModuleCat R)} (φ : K ⟶ L) :
    (ModuleCat.extendScalars f).map (ShortComplex.homologyMap φ) ≫ map f L =
      map f K ≫ ShortComplex.homologyMap
        ((ModuleCat.extendScalars f).mapShortComplex.map φ) := sorry

/-- Scalar-extension homology comparisons, bundled as a natural transformation on short
complexes. -/
noncomputable def natTrans (f : R →+* S) :
    ShortComplex.homologyFunctor (ModuleCat R) ⋙ ModuleCat.extendScalars f ⟶
      (ModuleCat.extendScalars f).mapShortComplex ⋙
        ShortComplex.homologyFunctor (ModuleCat S) where
  app K := map f K
  naturality _ _ φ := naturality f φ

/-- The homology comparison is surjective when the cokernel of the outgoing
differential is flat over the base ring. -/
@[stacks 063Q "surjective short-complex homology comparison from a flat cokernel"]
theorem surjective (f : R →+* S) (K : ShortComplex (ModuleCat R))
    [Module.Flat R (outgoingCokernel K)] :
    Function.Surjective (map (R := R) (S := S) f K).hom := sorry

/-- With a flat outgoing cokernel, the homology comparison is an epimorphism. -/
instance epi (f : R →+* S) (K : ShortComplex (ModuleCat R))
    [Module.Flat R (outgoingCokernel K)] :
    Epi (map (R := R) (S := S) f K) := sorry

/-- With a flat outgoing cokernel, vanishing of scalar-extended source homology implies
vanishing of the homology of the scalar-extended complex. -/
theorem isZero_of_source (f : R →+* S) (K : ShortComplex (ModuleCat R))
    [Module.Flat R (outgoingCokernel K)]
    (h : IsZero ((ModuleCat.extendScalars f).obj K.homology)) :
    IsZero ((K.map (ModuleCat.extendScalars f)).homology) := sorry

end HomologyComparison

end ExtendScalars

/-- Flat extension of scalars commutes with the homology of a short complex. -/
@[stacks 03B8 "short-complex homology under flat extension of scalars",
  stacks 09PQ "short-complex homology under flat extension of scalars"]
noncomputable def extendScalarsShortComplexHomologyIso
    (f : R →+* S) (hf : f.Flat) (K : ShortComplex (ModuleCat R)) :
    (K.map (ModuleCat.extendScalars f)).homology ≅
      (ModuleCat.extendScalars f).obj K.homology :=
  K.mapHomologyIso (ModuleCat.ExtendScalars.exact f hf).obj

/-- Restriction of scalars commutes with the homology of a short complex. -/
@[stacks 03B8 "short-complex homology under restriction of scalars",
  stacks 09PQ "short-complex homology under restriction of scalars"]
noncomputable def restrictScalarsShortComplexHomologyIso
    (f : R →+* S) (K : ShortComplex (ModuleCat S)) :
    (K.map (ModuleCat.restrictScalars f)).homology ≅
      (ModuleCat.restrictScalars f).obj K.homology :=
  K.mapHomologyIso (ModuleCat.RestrictScalars.exact f).obj

end ModuleCat
