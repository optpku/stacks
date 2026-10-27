/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.HomotopyLimit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme.LeftDerived

/-!
# Relative pseudo-coherence of formal-system homotopy limits

The quasi-coherent coreflection of an ambient homotopy limit of the pushed stage
sheaves of a proper flat formal system is pseudo-coherent relative to the
inverse-limit ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- The quasi-coherent coreflection of an ambient homotopy limit of the compatible
pushed stage sheaves of a proper flat formal system is pseudo-coherent relative to
the inverse-limit ring. -/
theorem coheratorHomotopyLimit_isPseudoCoherentOver (S : ProperFlatFormalSystem)
    [∀ sq : EtaleSquare (toBase S.space),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (stageIso_naturality : ∀ n,
      (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ pushforwardStep S n)
    (Klim : ModuleDerived S.space)
    (hKlim : HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor S.space.Modules (0 : ℤ)) Klim) :
    @ModuleDerived.IsPseudoCoherentOver _ _ _ (toBase S.space)
      (@locallyOfFiniteType_of_locallyOfFinitePresentation _ _ _ (toBase S.space)
        S.toBase_finitePresentation.toLocallyOfFinitePresentation)
      ((DerivedQCoh.inclusion S.space).rightAdjoint.obj Klim).obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
