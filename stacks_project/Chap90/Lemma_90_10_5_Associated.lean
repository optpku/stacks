module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Associated

/-!
# Associated functor of isomorphism classes

The covariant functor sending an object `A` of `ArtinianLocalAlgCat Λ k` to the type of
isomorphism classes in the fibre of a cofibered groupoid `p` over `A`.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

#check (CategoryTheory.Functor.isoClassFunctor :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op],
    ArtinianLocalAlgCat Λ k ⥤ Type v)

#check (CategoryTheory.Functor.isoClassFunctor_obj :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
      (A : ArtinianLocalAlgCat Λ k),
    (isoClassFunctor p).obj A = isomorphismClasses.obj (Cat.of ((p.op).Fiber (op A))))

#check (CategoryTheory.Functor.isoClassFunctor_map_mk :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
      (χ : (p.op).Cleavage) {A B : ArtinianLocalAlgCat Λ k}
      (f : A ⟶ B) (x : (p.op).Fiber (op A)),
    (isoClassFunctor p).map f (Quotient.mk'' x) = Quotient.mk'' ((f.op)⁎[χ] x))

#check (CategoryTheory.Functor.isoClassFunctor_op_isFiberedInGroupoids :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op],
    IsFibered.InGroupoids (CategoryOfElements.π (isoClassFunctor p)).op)

end CategoryTheory.Functor
