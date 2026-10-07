module

public import stacks_project.Chap98.Lemma_98_27_16_Versal

/-!
# Openness of versality for Type-valued functors

A Type-valued functor on locally Noetherian schemes over a locally Noetherian
base satisfies openness of versality when versality of a section at a finite
type point spreads to every finite type point of some open neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace (ofOver homOnLocallyNoetherian)

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Over

/-- A Type-valued functor on locally Noetherian schemes over a locally Noetherian
base `S` satisfies openness of versality when versality of a section on a
scheme locally of finite type over `S` at a finite type point spreads to an
open neighbourhood of finite type points. -/
class OpennessOfVersality {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v) : Prop where
  /-- Versality at a finite type point spreads to an open neighbourhood. -/
  exists_nhd :
    ∀ {V : Over S} [IsLocallyNoetherian V.left] [LocallyOfFiniteType V.hom]
      (ξ : F.obj (op (asLocallyNoetherian V))) (v0 : V.left),
      IsFiniteTypePoint v0 → IsVersalAt F ξ v0 →
        ∃ V' : V.left.Opens, v0 ∈ V' ∧
          ∀ v : V.left, v ∈ V' → IsFiniteTypePoint v → IsVersalAt F ξ v

/-- The representable functor `Mor_S(-, V)` on locally Noetherian schemes over
`S` satisfies openness of versality. -/
instance instOpennessOfVersality_hom {S : Scheme.{u}} [IsLocallyNoetherian S]
    (V : Over S) [IsLocallyNoetherian V.left] [LocallyOfFiniteType V.hom] :
    OpennessOfVersality (homOnLocallyNoetherian (ofOver V)) :=
  sorry

namespace OpennessOfVersality

/-- Openness of versality supplies an open neighbourhood of finite type points
on which versality persists. -/
theorem spec {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    [OpennessOfVersality F] {V : Over S} [IsLocallyNoetherian V.left]
    [LocallyOfFiniteType V.hom] (ξ : F.obj (op (asLocallyNoetherian V)))
    (v0 : V.left) (hv0 : IsFiniteTypePoint v0) (hvers : IsVersalAt F ξ v0) :
    ∃ V' : V.left.Opens, v0 ∈ V' ∧
      ∀ v : V.left, v ∈ V' → IsFiniteTypePoint v → IsVersalAt F ξ v :=
  sorry

/-- Openness of versality is the neighbourhood spreading of versality at finite
type points. -/
theorem iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v) :
    OpennessOfVersality F ↔
      ∀ {V : Over S} [IsLocallyNoetherian V.left] [LocallyOfFiniteType V.hom]
        (ξ : F.obj (op (asLocallyNoetherian V))) (v0 : V.left),
        IsFiniteTypePoint v0 → IsVersalAt F ξ v0 →
          ∃ V' : V.left.Opens, v0 ∈ V' ∧
            ∀ v : V.left, v ∈ V' → IsFiniteTypePoint v → IsVersalAt F ξ v :=
  sorry

end OpennessOfVersality

/-- Unfolding `OpennessOfVersality` recovers the neighbourhood quantifier. -/
theorem opennessOfVersality_iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v) :
    OpennessOfVersality F ↔
      ∀ {V : Over S} [IsLocallyNoetherian V.left] [LocallyOfFiniteType V.hom]
        (ξ : F.obj (op (asLocallyNoetherian V))) (v0 : V.left),
        IsFiniteTypePoint v0 → IsVersalAt F ξ v0 →
          ∃ V' : V.left.Opens, v0 ∈ V' ∧
            ∀ v : V.left, v ∈ V' → IsFiniteTypePoint v → IsVersalAt F ξ v :=
  sorry

end AlgebraicGeometry.Scheme.Over
