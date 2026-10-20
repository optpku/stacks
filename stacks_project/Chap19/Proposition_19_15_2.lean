module

public import ReasLib.CategoryTheory.DerivedCategory.BrownRepresentability.Grothendieck
import StacksCheckRecall

@[expose] public section

/-!
# Exact Right Adjoints from Brown Representability

The chapter entry is a direct specialization of the Brown-set adjoint-functor API for
Grothendieck derived categories.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u v' u'

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{max u v} A] [IsGrothendieckAbelian.{max u v} A]
variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
  [LocallySmall.{max u v} D] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]

/- Proposition 19.15.2: an exact coproduct-preserving functor `D(A) ⥤ D` admits an exact right
adjoint. -/
@[stacks 0F5Y] #check
  fun (F : DerivedCategory A ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
      [∀ J : Type (max u v), PreservesColimitsOfShape (Discrete J) F] ↦
    (Functor.Brown.Grothendieck.hasTriangulatedRightAdjoint F :
      ∃ (G : D ⥤ DerivedCategory A) (adj : F ⊣ G),
        G.IsTriangulatedWith (adj.rightAdjointCommShift ℤ))
