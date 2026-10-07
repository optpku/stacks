module

public import stacks_project.Chap88.«88_27_0_1_Completion»

/-!
# Factorization through a locally finite-type monomorphism after checking the open complement and the completion

A morphism of algebraic spaces that factors through a locally finite-type
monomorphism both on the open complement of a closed subset and on the
completion along that subset factors through the monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- Lemma 88.25.3: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of algebraic spaces. Let `T ⊂ Points X` be closed. Assume that `X`
is locally Noetherian, `g` is a monomorphism and locally of finite type,
`f|_{X \ T} : X \ T ⟶ Y` factors through `g`, and `f_/T : X_/T ⟶ Y` factors
through `g`. Then `f` factors through `g`.

Here `f|_{X \ T}` is `openComplementι X T ≫ f : openComplementAlong X T ⟶ Y`,
and `f_/T` is `ι X T ≫ f : completionAlong X T ⟶ Y.functorOfPoints`. -/
@[stacks 0AR6]
theorem exists_factorThrough {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X ⟶ Y) (g : Z ⟶ Y)
    [Mono g] [LocallyOfFiniteType g]
    (h_open : ∃ h : openComplementAlong X T ⟶ Z, h ≫ g = openComplementι X T ≫ f)
    (h_completion : ∃ h : completionAlong X T ⟶ Z.functorOfPoints,
      h ≫ g = ι X T ≫ f) :
    ∃ h : X ⟶ Z, h ≫ g = f :=
  sorry

/-- Uniqueness of the factorization through `g` in `exists_factorThrough`,
which follows because `g` is a monomorphism. -/
theorem existsUnique_factorThrough {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X ⟶ Y) (g : Z ⟶ Y)
    [Mono g] [LocallyOfFiniteType g]
    (h_open : ∃ h : openComplementAlong X T ⟶ Z, h ≫ g = openComplementι X T ≫ f)
    (h_completion : ∃ h : completionAlong X T ⟶ Z.functorOfPoints,
      h ≫ g = ι X T ≫ f) :
    ∃! h : X ⟶ Z, h ≫ g = f :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
