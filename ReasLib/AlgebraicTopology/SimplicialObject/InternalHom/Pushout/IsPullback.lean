/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Variance
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.RepresentableBy.Variance
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Internal hom sends pushouts to pullbacks

This leaf records the assumption-minimal categorical statement for simplicial internal hom.
The chosen comparison morphisms, explicit inverses, and target naturality API are layered in
`SimplicialObject.InternalHom.Pushout`.
-/

@[expose] public section

universe vC uC uS

namespace CategoryTheory.IsPushout

variable {C : Type uC} [Category.{vC} C]
variable {U V W P : SSet.{uS}} {a : U ⟶ V} {b : U ⟶ W}
variable {inl : V ⟶ P} {inr : W ⟶ P}

/-- Applying the contravariant simplicial internal-hom construction, presented by arbitrary
explicit representing objects, to a pushout square gives a pullback square. -/
@[stacks 017N "explicit internal hom sends simplicial-set pushouts to pullbacks"]
theorem internalHomOf (h : IsPushout a b inl inr) (T : SimplicialObject C)
    [SimplicialObject.HasCopowers U C] [SimplicialObject.HasCopowers V C]
    [SimplicialObject.HasCopowers W C] [SimplicialObject.HasCopowers P C]
    {MU MV MW MP : SimplicialObject C}
    (RU : (SimplicialObject.internalHom.presheaf U T).RepresentableBy MU)
    (RV : (SimplicialObject.internalHom.presheaf V T).RepresentableBy MV)
    (RW : (SimplicialObject.internalHom.presheaf W T).RepresentableBy MW)
    (RP : (SimplicialObject.internalHom.presheaf P T).RepresentableBy MP) :
    IsPullback
      (SimplicialObject.internalHom.precompOf inl RV RP)
      (SimplicialObject.internalHom.precompOf inr RW RP)
      (SimplicialObject.internalHom.precompOf a RU RV)
      (SimplicialObject.internalHom.precompOf b RU RW) := sorry

/-- Applying the contravariant simplicial internal-hom construction to a pushout square of
indexing simplicial sets gives a pullback square. This is the specialization of `internalHomOf`
to the canonical representing objects. -/
@[stacks 017N "internal hom sends simplicial-set pushouts to pullbacks"]
theorem internalHom (h : IsPushout a b inl inr) (T : SimplicialObject C)
    [SimplicialObject.HasCopowers U C] [SimplicialObject.HasCopowers V C]
    [SimplicialObject.HasCopowers W C] [SimplicialObject.HasCopowers P C]
    [SimplicialObject.HasInternalHom U T] [SimplicialObject.HasInternalHom V T]
    [SimplicialObject.HasInternalHom W T] [SimplicialObject.HasInternalHom P T] :
    IsPullback
      (SimplicialObject.internalHom.precomp inl T)
      (SimplicialObject.internalHom.precomp inr T)
      (SimplicialObject.internalHom.precomp a T)
      (SimplicialObject.internalHom.precomp b T) := sorry

end CategoryTheory.IsPushout
