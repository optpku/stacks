module

public import ReasLib.CategoryTheory.Filtration.Derived.Quotient
public import ReasLib.CategoryTheory.Filtration.Derived.AssociatedGraded
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteAcyclic
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteHomology
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization.Lift
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangulated Finite Filtered Derived Categories

The quotient data lives in `Derived.Quotient`.  This leaf adds the independent additive and
triangulated enhancement: finite filtered objects are additive with binary biproducts, and the
remaining assertions that filtered quasi-isomorphisms admit Verdier calculus are Prop-valued
proof obligations.  This separation keeps the canonical localization carrier free of those
proof debts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]

namespace Acyclic

/-- Finite filtered acyclic complexes are the homological kernel of degree-zero homology after
the finite associated-graded functor. -/
@[stacks 05S1 "finite filtered acyclic homological kernel"]
theorem eqHomologicalKernel :
    FilteredObject.Finite.Homotopy.acyclic C =
      (Finite.AssociatedGraded.Homology.zero C).homologicalKernel := sorry

/-- The Verdier morphism property of finite filtered acyclic complexes is the finite filtered
quasi-isomorphism property. -/
@[stacks 05S1 "finite filtered quasi-isomorphism"]
theorem trW_eq_quasiIso :
    (FilteredObject.Finite.Homotopy.acyclic C).trW = FilteredObject.Finite.Homotopy.quasiIso C := sorry

/-- The kernel of localization at finite filtered quasi-isomorphisms is the finite filtered
acyclic subcategory. -/
@[stacks 05S1 "finite filtered quasi-isomorphism localization"]
theorem kernel_eq :
    Functor.kernel
        ((Quotient.functor C) :
          HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ) ⥤
            Quotient.Category C) =
      FilteredObject.Finite.Homotopy.acyclic C := sorry

/-- Degree-zero homology after finite associated graded factors through the finite filtered
derived localization. -/
@[stacks 05S1 "finite filtered associated graded homology"]
theorem existsHomologyFactorization :
    ∃ H' : Quotient.Category C ⥤ GradedObject ℤ C,
      Quotient.functor C ⋙ H' = Finite.AssociatedGraded.Homology.zero C := sorry

/-- Finite filtered acyclic complexes form a strictly full subcategory. -/
@[stacks 05S1 "finite filtered acyclic subcategory"]
instance isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (FilteredObject.Finite.Homotopy.acyclic C) := sorry

/-- Finite filtered acyclic complexes are stable under retracts. -/
@[stacks 05S1 "finite filtered acyclic subcategory"]
instance isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts (FilteredObject.Finite.Homotopy.acyclic C) := sorry

/-- Finite filtered acyclic complexes form a triangulated subcategory. -/
@[stacks 05S1 "finite filtered acyclic subcategory"]
instance isTriangulated :
    ObjectProperty.IsTriangulated (FilteredObject.Finite.Homotopy.acyclic C) := sorry

end Acyclic

namespace QuasiIso

/-- Finite filtered quasi-isomorphisms admit a left calculus of fractions.  This is the
Prop-valued Verdier input needed to enhance their already-constructed localization. -/
@[stacks 05S2 "finite filtered quasi-isomorphism localization"]
instance hasLeftCalculus :
    (FilteredObject.Finite.Homotopy.quasiIso C).HasLeftCalculusOfFractions := sorry

/-- Finite filtered quasi-isomorphisms are compatible with the triangulation of the finite
filtered homotopy category. -/
@[stacks 05S2 "finite filtered quasi-isomorphism localization"]
instance compatibleWithTriangulation :
    (FilteredObject.Finite.Homotopy.quasiIso C).IsCompatibleWithTriangulation := sorry

/-- Finite filtered quasi-isomorphisms form a saturated multiplicative system. -/
@[stacks 05S1 "finite filtered quasi-isomorphism"]
instance isSaturated :
    IsSaturatedMultiplicativeSystem (FilteredObject.Finite.Homotopy.quasiIso C) := sorry

end QuasiIso

namespace Quotient

namespace Category

/-- The finite filtered derived localization is preadditive. -/
@[stacks 05S2 "finite filtered derived category"]
noncomputable instance preadditive : Preadditive (Quotient.Category C) :=
  inferInstance

/-- The finite filtered derived localization has a zero object. -/
@[stacks 05S2 "finite filtered derived category"]
noncomputable instance hasZeroObject : HasZeroObject (Quotient.Category C) :=
  inferInstance

/-- The finite filtered derived localization has the induced integer shift. -/
@[stacks 05S2 "finite filtered derived category"]
noncomputable instance hasShift : HasShift (Quotient.Category C) ℤ :=
  inferInstance

/-- The finite filtered derived localization is pretriangulated. -/
@[stacks 05S2 "finite filtered derived category"]
noncomputable instance pretriangulated : Pretriangulated (Quotient.Category C) :=
  inferInstance

/-- The finite filtered derived localization is triangulated. -/
@[stacks 05S2 "finite filtered derived category"]
noncomputable instance isTriangulated : IsTriangulated (Quotient.Category C) :=
  inferInstance

end Category

namespace Functor

/-- The finite filtered derived quotient functor commutes with shifts. -/
@[stacks 05S2 "finite filtered derived quotient functor"]
noncomputable instance commShift :
    (Quotient.functor C).CommShift ℤ :=
  inferInstance

/-- The finite filtered derived quotient functor is exact. -/
@[stacks 05S2 "finite filtered derived quotient functor"]
noncomputable instance isTriangulated :
    (Quotient.functor C).IsTriangulated :=
  inferInstance

end Functor

end Quotient

namespace AssociatedGraded

variable [HasDerivedCategory (GradedObject ℤ C)]

namespace Homotopy

/-- The finite associated-graded homotopy-to-derived functor is exact. -/
@[stacks 05S3 "finite filtered associated graded derived functor"]
noncomputable instance isTriangulated :
    (AssociatedGraded.homotopy C).IsTriangulated :=
  inferInstanceAs
    ((Finite.AssociatedGraded.homotopy C ⋙ DerivedCategory.Qh).IsTriangulated)

end Homotopy

namespace Lift

/-- The finite derived associated-graded lift commutes with integer shifts.

This is the canonical `CommShift` structure transported through the finite filtered
localization; its inversion certificate is explicit because it selects the corresponding
localization lift. -/
@[stacks 05S3 "finite filtered associated graded derived functor"]
noncomputable instance commShift (h_inverts : AssociatedGraded.Inverts C) :
    (AssociatedGraded.lift C h_inverts).CommShift ℤ :=
  CategoryTheory.Localization.liftCommShift
    (FilteredObject.Finite.Homotopy.quasiIso C) (Quotient.functor C) (AssociatedGraded.homotopy C) h_inverts

/-- The finite derived associated-graded functor is exact once the finite filtered localization
has its Verdier enhancement.  The descent certificate remains explicit because it is not
canonical data of the localization itself. -/
@[stacks 05S3 "finite filtered associated graded derived functor"]
instance isTriangulated (h_inverts : AssociatedGraded.Inverts C) :
    (AssociatedGraded.lift C h_inverts).IsTriangulated :=
  CategoryTheory.Localization.lift_isTriangulated
    (FilteredObject.Finite.Homotopy.quasiIso C) (Quotient.functor C) (AssociatedGraded.homotopy C) h_inverts

end Lift

namespace FacIso

/-- The forward finite associated-graded factorization comparison commutes with shifts. -/
@[stacks 05S3 "finite filtered associated graded factorization"]
noncomputable instance homCommShift (h_inverts : AssociatedGraded.Inverts C) :
    NatTrans.CommShift (AssociatedGraded.facIso C h_inverts).hom ℤ := sorry

/-- The inverse finite associated-graded factorization comparison commutes with shifts. -/
@[stacks 05S3 "finite filtered associated graded factorization"]
noncomputable instance invCommShift (h_inverts : AssociatedGraded.Inverts C) :
    NatTrans.CommShift (AssociatedGraded.facIso C h_inverts).inv ℤ := sorry

end FacIso

end AssociatedGraded

namespace GradedPiece

variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject ℤ C)]

namespace Homotopy

/-- Each finite associated-graded-piece homotopy-to-derived functor commutes with shifts. -/
@[stacks 05S3 "finite filtered derived graded piece"]
noncomputable instance commShift (p : ℤ) :
    (GradedPiece.homotopy C p).CommShift ℤ :=
  Functor.CommShift.ofIso (GradedPiece.compIso C p) ℤ

/-- The comparison from derived associated graded to a derived graded piece commutes with shifts. -/
@[stacks 05S3 "finite filtered derived graded piece"]
noncomputable instance compIsoCommShift (p : ℤ) :
    NatTrans.CommShift (GradedPiece.compIso C p).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (GradedPiece.compIso C p) ℤ

/-- Each finite associated-graded-piece homotopy-to-derived functor is exact. -/
@[stacks 05S3 "finite filtered derived graded piece"]
noncomputable instance isTriangulated (p : ℤ) :
    (GradedPiece.homotopy C p).IsTriangulated :=
  Functor.isTriangulated_of_iso (GradedPiece.compIso C p)

end Homotopy

namespace Lift

/-- Each finite derived associated-graded piece commutes with integer shifts. -/
@[stacks 05S3 "finite filtered derived graded piece"]
noncomputable instance commShift
    (h_inverts : AssociatedGraded.Inverts C) (p : ℤ) :
    (GradedPiece.lift C h_inverts p).CommShift ℤ :=
  inferInstanceAs
    ((AssociatedGraded.lift C h_inverts ⋙
      (GradedObject.eval p).mapDerivedCategory).CommShift ℤ)

/-- Each finite derived associated-graded piece is exact once the finite filtered localization
has its Verdier enhancement. -/
@[stacks 05S3 "finite filtered derived graded piece"]
instance isTriangulated
    (h_inverts : AssociatedGraded.Inverts C) (p : ℤ) :
    (GradedPiece.lift C h_inverts p).IsTriangulated :=
  inferInstanceAs
    ((AssociatedGraded.lift C h_inverts ⋙
      (GradedObject.eval p).mapDerivedCategory).IsTriangulated)

end Lift

namespace FacIso

/-- The forward finite graded-piece factorization comparison commutes with shifts. -/
@[stacks 05S3 "finite filtered graded piece factorization"]
noncomputable instance homCommShift
    (h_inverts : AssociatedGraded.Inverts C) (p : ℤ) :
    NatTrans.CommShift (GradedPiece.facIso C h_inverts p).hom ℤ := sorry

/-- The inverse finite graded-piece factorization comparison commutes with shifts. -/
@[stacks 05S3 "finite filtered graded piece factorization"]
noncomputable instance invCommShift
    (h_inverts : AssociatedGraded.Inverts C) (p : ℤ) :
    NatTrans.CommShift (GradedPiece.facIso C h_inverts p).inv ℤ := sorry

end FacIso

end GradedPiece

variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C) (p : ℤ)

#synth NatTrans.CommShift (AssociatedGraded.facIso C h_inverts).hom ℤ
#synth NatTrans.CommShift (GradedPiece.facIso C h_inverts p).hom ℤ

end CategoryTheory.FilteredObject.FiniteDerived
