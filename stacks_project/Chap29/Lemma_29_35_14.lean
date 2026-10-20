/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.LocalCriterion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

universe u

/- Lemma 29.35.14: For a scheme morphism locally of finite type, unramifiedness at a point is
equivalent to unramifiedness of its residue-field fibre there, vanishing of the two relevant
differential stalks and cotangent space, and the maximal-ideal equality with finite separable
residue-field extension. -/
@[stacks 02GF] #check
  (AlgebraicGeometry.unramifiedAt_tfae_differentials_fiber_residueField :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X) [LocallyOfFiniteType f],
      List.TFAE [
        f.UnramifiedAt x,
        (f.fiberToSpecResidueField (f x)).UnramifiedAt (f.asFiber x),
        IsZero (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x),
        IsZero
          (RingedSpace.stalkModuleCat
            (Ω[(f.fiberToSpecResidueField (f x)).toShHom]) (f.asFiber x)),
        Subsingleton
          ((IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗[(X.presheaf.stalk x)]
            (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x)),
        MaximalIdealResidueFieldUnramifiedAtCriterion f x])

/- The locally finite presentation variant replaces pointwise unramifiedness by pointwise
G-unramifiedness while retaining ordinary unramifiedness of the residue-field fibre. -/
#check
  (AlgebraicGeometry.gUnramifiedAt_tfae_differentials_fiber_residueField :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X) [LocallyOfFinitePresentation f],
      List.TFAE [
        f.GUnramifiedAt x,
        (f.fiberToSpecResidueField (f x)).UnramifiedAt (f.asFiber x),
        IsZero (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x),
        IsZero
          (RingedSpace.stalkModuleCat
            (Ω[(f.fiberToSpecResidueField (f x)).toShHom]) (f.asFiber x)),
        Subsingleton
          ((IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗[(X.presheaf.stalk x)]
            (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x)),
        MaximalIdealResidueFieldUnramifiedAtCriterion f x])
