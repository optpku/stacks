module

public import ReasLib.CategoryTheory.SerreFunctor.Structure
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.SerreFunctor

variable {T : Type u} [Category.{v} T] [Preadditive T]

/-- A natural isomorphism between Serre functors is compatible when it preserves their
Hom-duality pairings. -/
def IsCompatible {k : Type w} [Field k] [Linear k T]
    (S S' : SerreFunctor k T)
    (e : S.toEquivalence.functor ≅ S'.toEquivalence.functor) : Prop :=
  ∀ (X Y : T) (f : X ⟶ Y) (h : Y ⟶ Functor.obj S.toEquivalence.functor X),
    S.pairing X Y f h = S'.pairing X Y f (h ≫ (e.app X).hom)

/-- Any two Serre functors on a Hom-finite triangulated category are uniquely isomorphic
through a natural isomorphism compatible with their Hom-duality pairings. -/
theorem uniqueIso
    {k : Type w} [Field k] [Linear k T]
    [Limits.HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
    (hfinite : ∀ X Y : T, FiniteDimensional k (X ⟶ Y))
    (S S' : SerreFunctor k T) :
    ∃! e : S.toEquivalence.functor ≅ S'.toEquivalence.functor,
      IsCompatible S S' e := sorry

end CategoryTheory.SerreFunctor

end
