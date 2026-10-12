/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Contraction
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Weight

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsContraction

/-- A surviving component has positive constant-field degree dividing its original degree. -/
theorem componentWeight_dvd_source
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X X' : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    [Flat p] [Scheme.Hom.FiniteType p] [IsProper p] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin (n + 1) ≃
      irreducibleComponents (p.fiber (IsLocalRing.closedPoint R)))
    [IsNoetherian X]
    [IsExceptionalCurveFirstKind
      (p.specialFiberComponent (components (Fin.last n)))]
    (b : X ⟶ X') (x : closedPoints X')
    (hb : IsContraction
      (p.specialFiberComponent (components (Fin.last n))) b x)
    (p' : X' ⟶ Spec (CommRingCat.of R))
    [IsNoetherian X'] [Flat p'] [Scheme.Hom.FiniteType p'] [IsProper p']
    [Scheme.Regular X']
    (genericFiberIso' : C ≅ Over.mk
      (pullback.snd p' (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (components' : Fin n ≃
      irreducibleComponents (p'.fiber (IsLocalRing.closedPoint R)))
    (h_over : b ≫ p' = p)
    (h_image : ∀ i : Fin n,
      (p.specialFiberComponent (components i.castSucc)).map b =
        p'.specialFiberComponent (components' i)) :
    ∀ i : Fin n,
      0 < Scheme.Hom.SpecialFiber.componentWeight p' (components' i) ∧
        Scheme.Hom.SpecialFiber.componentWeight p' (components' i) ∣
          Scheme.Hom.SpecialFiber.componentWeight p (components i.castSucc) := sorry

/-- If the surviving component meets the exceptional component, its image degree also
divides the exceptional degree. -/
theorem componentWeight_dvd_exceptional
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X X' : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    [Flat p] [Scheme.Hom.FiniteType p] [IsProper p] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin (n + 1) ≃
      irreducibleComponents (p.fiber (IsLocalRing.closedPoint R)))
    [IsNoetherian X]
    [IsExceptionalCurveFirstKind
      (p.specialFiberComponent (components (Fin.last n)))]
    (b : X ⟶ X') (x : closedPoints X')
    (hb : IsContraction
      (p.specialFiberComponent (components (Fin.last n))) b x)
    (p' : X' ⟶ Spec (CommRingCat.of R))
    [IsNoetherian X'] [Flat p'] [Scheme.Hom.FiniteType p'] [IsProper p']
    [Scheme.Regular X']
    (genericFiberIso' : C ≅ Over.mk
      (pullback.snd p' (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (components' : Fin n ≃
      irreducibleComponents (p'.fiber (IsLocalRing.closedPoint R)))
    (h_over : b ≫ p' = p)
    (h_image : ∀ i : Fin n,
      (p.specialFiberComponent (components i.castSucc)).map b =
        p'.specialFiberComponent (components' i)) :
    ∀ i : Fin n,
      Set.Nonempty
        (((p.specialFiberComponent (components i.castSucc)).support : Set X) ∩
          ((p.specialFiberComponent (components (Fin.last n))).support : Set X)) →
        Scheme.Hom.SpecialFiber.componentWeight p' (components' i) ∣
          Scheme.Hom.SpecialFiber.componentWeight p (components (Fin.last n)) := sorry

end AlgebraicGeometry.IsContraction
