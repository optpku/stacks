module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Fppf locality of algebraic spaces of finite type

A sheaf which is fppf locally an algebraic space of finite type over the
cover is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Package `yoneda.obj U ⨯ F` as an algebraic space over `S` from an explicit
`IsAlgebraicSpace` hypothesis. -/
def ofYonedaProd {S : Scheme.{u}} {U : Over S} {F : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsAlgebraicSpace (yoneda.obj U ⨯ F)) : AlgebraicSpace S :=
  ofFunctor (yoneda.obj U ⨯ F) h.isSheaf h.representableDiagonal h.atlas

/-- The functor of points of `ofYonedaProd h` is `yoneda.obj U ⨯ F`. -/
theorem ofYonedaProd_functorOfPoints {S : Scheme.{u}} {U : Over S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (h : IsAlgebraicSpace (yoneda.obj U ⨯ F)) :
    (ofYonedaProd h).functorOfPoints = (yoneda.obj U ⨯ F) :=
  sorry

/-- The structure morphism `Fᵢ ⟶ Sᵢ` of the fibre product algebraic space
`yoneda.obj U ⨯ F`. -/
def yonedaProdFst {S : Scheme.{u}} {U : Over S} {F : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsAlgebraicSpace (yoneda.obj U ⨯ F)) : ofYonedaProd h ⟶ ofOver U :=
  (prod.fst : yoneda.obj U ⨯ F ⟶ yoneda.obj U)

/-- `yonedaProdFst h` is the functor-category projection `prod.fst`. -/
theorem yonedaProdFst_eq {S : Scheme.{u}} {U : Over S} {F : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsAlgebraicSpace (yoneda.obj U ⨯ F)) :
    yonedaProdFst h = (prod.fst : yoneda.obj U ⨯ F ⟶ yoneda.obj U) :=
  sorry

/-- Lemma 80.11.2: let `S` be a scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a
functor. Let `{Sᵢ → S}_{i ∈ I}` be a covering of `(Sch/S)_fppf`. If `F` is an
fppf sheaf, each `Fᵢ = yoneda.obj (Sᵢ) ⨯ F` is an algebraic space, and each
structure morphism `yonedaProdFst : Fᵢ ⟶ Sᵢ` is of finite type, then `F` is an
algebraic space. Finite type of `Fᵢ ⟶ Sᵢ` replaces the `[Small.{u} I]` size
condition of Lemma 80.11.1 / Spaces, Lemma 65.8.4. -/
@[stacks 04U0]
theorem IsAlgebraicSpace.of_fppfLocal_finiteType {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {I : Type v}
    (Si : I → Over S) (hSi : Scheme.FppfCovering Si)
    (hFi : ∀ i, IsAlgebraicSpace (yoneda.obj (Si i) ⨯ F))
    (h_finiteType : ∀ i, FiniteType (yonedaProdFst (hFi i))) :
    IsAlgebraicSpace F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
