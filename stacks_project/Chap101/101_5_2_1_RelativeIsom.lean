module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Diagonal.RelativeIsom

/-!
# Relative automorphism presheaf compatibility checks

For a morphism of groupoid fibrations, `Isom_{X/Y}(x, x)` is the kernel of
`Isom_X(x, x) ⟶ Isom_Y(f(x), f(x))` at the identity section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

#check (identitySection : ∀ (f : X ⟶ Y) {T : Over S} (x : X.p.Fiber T),
    (isom ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x)).obj
      (op (Over.mk (𝟙 T))))

#check (constIdentity : ∀ (f : X ⟶ Y) {T : Over S} (x : X.p.Fiber T),
    isom x x ⟶
      isom ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x))

#check (relativeIsom : ∀ (f : X ⟶ Y) {T : Over S} (x : X.p.Fiber T),
    (Over T)ᵒᵖ ⥤ Type (u + 1))

#check (relativeIsom.ι : ∀ (f : X ⟶ Y) {T : Over S} (x : X.p.Fiber T),
    relativeIsom f x ⟶ isom x x)

#check (relativeIsom.condition : ∀ (f : X ⟶ Y) {T : Over S} (x : X.p.Fiber T),
    relativeIsom.ι f x ≫ isomMap f x x =
      relativeIsom.ι f x ≫ constIdentity f x)

#check (mem_relativeIsom_iff : ∀ (f : X ⟶ Y) {T : Over S} (x : X.p.Fiber T)
    {T' : Over T} (φ : (isom x x).obj (op T')),
    (∃ ψ : (relativeIsom f x).obj (op T'),
        (relativeIsom.ι f x).app (op T') ψ = φ) ↔
      (isomMap f x x).app (op T') φ =
        (constIdentity f x).app (op T') φ)

end CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal
