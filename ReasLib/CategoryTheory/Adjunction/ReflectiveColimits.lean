/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v u' v' w w'

namespace CategoryTheory.Adjunction
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- An actual mapped colimit witness constructed from a specified adjunction. -/
def mapColimitWitness {J : Type w} [Category.{w'} J] {K : J ⥤ C}
    {c : Cocone K} (hc : IsColimit c) : IsColimit (L.mapCocone c) :=
  IsColimit.isoUniqueCoconeMorphism.inv fun _ ↦
    @Equiv.unique _ _ (IsColimit.isoUniqueCoconeMorphism.hom hc _)
      ((adj.functorialityAdjunction _).homEquiv _ _)

/-- Transfer an explicit colimit construction through a reflective presentation. All cocone
maps come from the supplied witnesses and isomorphisms, rather than a preservation selector. -/
def reflectiveMapColimitWitness (e : R ⋙ L ≅ 𝟭 D)
    (S : C ⥤ C) (T : D ⥤ D) (comparison : S ⋙ L ≅ L ⋙ T)
    {J : Type w} [Category.{w'} J] {K : J ⥤ D} [HasColimit (K ⋙ R)]
    (mapS : ∀ {d : Cocone (K ⋙ R)}, IsColimit d → IsColimit (S.mapCocone d))
    {c : Cocone K} (hc : IsColimit c) : IsColimit (T.mapCocone c) := by
  let d := colimit.cocone (K ⋙ R)
  let hd := colimit.isColimit (K ⋙ R)
  let diagramIso : (K ⋙ R) ⋙ L ≅ K :=
    (Functor.associator K R L) ≪≫ Functor.isoWhiskerLeft K e ≪≫ K.rightUnitor
  let c' := (Cocone.precompose diagramIso.hom).obj c
  let hc' : IsColimit c' := (IsColimit.precomposeHomEquiv diagramIso c).symm hc
  let hdL := adj.mapColimitWitness hd
  let hdSL := adj.mapColimitWitness (mapS hd)
  let hdLT : IsColimit (T.mapCocone (L.mapCocone d)) :=
    IsColimit.mapCoconeEquiv comparison hdSL
  let hc'T : IsColimit (T.mapCocone c') :=
    hdLT.ofIsoColimit ((Cocone.functoriality _ T).mapIso (hdL.uniqueUpToIso hc'))
  exact (IsColimit.precomposeHomEquiv (Functor.isoWhiskerRight diagramIso T)
    (T.mapCocone c)) (hc'T.ofIsoColimit (Functor.mapCoconePrecompose T))

end CategoryTheory.Adjunction
