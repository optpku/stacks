module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Transport
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Domain
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Shift

@[expose] public section

/-!
# Shift Stability of Source-Defined Derived Values

Essential constancy of a localization-indexed diagram is invariant under the reindexing and
target equivalences induced by a shift.  This leaf records that fact independently of additive
or triangulated structures.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open MorphismProperty ObjectProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasShift D ℤ] [HasShift D' ℤ]
  (F : D ⥤ D') (S : MorphismProperty D)

namespace Functor.RightDerived.DefinedAt

namespace objects

/-- The object property where the right-derived indexing diagram is essentially constant is
stable under integer shifts. -/
@[stacks 05SC "shift-stable right-derived essential-constancy domain"]
instance isStableUnderShift [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] :
    IsStableUnderShift (Functor.RightDerived.DefinedAt.objects F S) ℤ := sorry

end objects

/-- Source-definedness of a pointwise right-derived value transports through an integer shift. -/
@[stacks 05SC "right-derived source-definedness after a shift"]
instance shift [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) [Functor.RightDerived.DefinedAt F S X] :
    Functor.RightDerived.DefinedAt F S (X⟦n⟧) := sorry

/-- Source-definedness of a pointwise right-derived value is invariant under every integer
shift. -/
@[stacks 05SC "shift stability of right-derived source-definedness"]
theorem iff_shift [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    Functor.RightDerived.DefinedAt F S X ↔
      Functor.RightDerived.DefinedAt F S (X⟦n⟧) := sorry

end Functor.RightDerived.DefinedAt

namespace Functor.LeftDerived.DefinedAt

namespace objects

/-- The object property where the left-derived indexing diagram is essentially constant is
stable under integer shifts. -/
@[stacks 05SC "shift-stable left-derived essential-constancy domain"]
instance isStableUnderShift [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] :
    IsStableUnderShift (Functor.LeftDerived.DefinedAt.objects F S) ℤ := sorry

end objects

/-- Source-definedness of a pointwise left-derived value transports through an integer shift. -/
@[stacks 05SC "left-derived source-definedness after a shift"]
instance shift [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) [Functor.LeftDerived.DefinedAt F S X] :
    Functor.LeftDerived.DefinedAt F S (X⟦n⟧) := sorry

/-- Source-definedness of a pointwise left-derived value is invariant under every integer
shift. -/
@[stacks 05SC "shift stability of left-derived source-definedness"]
theorem iff_shift [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    Functor.LeftDerived.DefinedAt F S X ↔
      Functor.LeftDerived.DefinedAt F S (X⟦n⟧) := sorry

end Functor.LeftDerived.DefinedAt


end CategoryTheory
