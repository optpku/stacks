/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Variance
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Pushout.ComparisonOf

/-!
# Chosen internal-hom comparisons for simplicial-set pushouts

This leaf specializes the explicit comparison API to the canonical representing objects selected
by `HasInternalHom`. It introduces no second owner for the underlying comparison data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject.internalHom.pushout

variable {C : Type uC} [Category.{vC} C]
variable {U V W : SSet.{uS}} (a : U ⟶ V) (b : U ⟶ W) (T : SimplicialObject C)
variable [HasCopowers U C] [HasCopowers V C] [HasCopowers W C]
variable [HasCopowers (pushout a b) C]
variable [HasInternalHom U T] [HasInternalHom V T] [HasInternalHom W T]
variable [HasInternalHom (pushout a b) T]

namespace comparison

/-- The two composites obtained by precomposing from the simplicial pushout agree over the source
of the span. -/
@[stacks 017N "compatibility for chosen internal-hom representations"]
theorem condition :
    precomp (CategoryTheory.Limits.pushout.inl a b) T ≫ precomp a T =
      precomp (CategoryTheory.Limits.pushout.inr a b) T ≫ precomp b T := sorry

/-- The objectwise comparison only needs the chosen internal-hom objects for its fixed target.
This bridge keeps that API independent of the stronger functor-wide `HasInternalHoms` assumptions. -/
@[stacks 017N "objectwise pullback for the canonical internal-hom comparison"]
instance (priority := 90) hasPullback :
    HasPullback (precomp a T) (precomp b T) :=
  (CategoryTheory.IsPushout.internalHom
    (show IsPushout a b (pushout.inl a b) (pushout.inr a b) from
      CategoryTheory.IsPushout.of_isColimit (pushout.isColimit a b)) T).hasPullback

end comparison

/-- The canonical morphism from the internal mapping object out of a pushout to the pullback of
the two precomposition morphisms. This is the canonical-representation specialization of
`comparisonOf`. -/
@[stacks 017N "internal-hom pushout comparison"]
def comparison :
    internalHom (CategoryTheory.Limits.pushout a b) T ⟶
      pullback (precomp a T) (precomp b T) :=
  comparisonOf a b (internalHom.representableBy U T)
    (internalHom.representableBy V T) (internalHom.representableBy W T)
    (internalHom.representableBy (pushout a b) T)

namespace comparison

/-- The first projection of `comparison` is precomposition by the left pushout coprojection. -/
@[reassoc (attr := simp), stacks 017N "first projection of the canonical internal-hom comparison"]
theorem fst :
    pushout.comparison a b T ≫ pullback.fst (precomp a T) (precomp b T) =
      precomp (CategoryTheory.Limits.pushout.inl a b) T := sorry

/-- The second projection of `comparison` is precomposition by the right pushout coprojection. -/
@[reassoc (attr := simp), stacks 017N "second projection of the canonical internal-hom comparison"]
theorem snd :
    pushout.comparison a b T ≫ pullback.snd (precomp a T) (precomp b T) =
      precomp (CategoryTheory.Limits.pushout.inr a b) T := sorry

namespace inv

/-- The maps represented by the canonical pullback projections agree after restriction to
the source of the simplicial-set span. -/
@[stacks 017N "compatibility for the inverse internal-hom pushout comparison"]
theorem condition :
    copower.indexHom (pullback (precomp a T) (precomp b T)) a ≫
        internalHom.homEquiv V T (pullback (precomp a T) (precomp b T))
          (pullback.fst (precomp a T) (precomp b T)) =
      copower.indexHom (pullback (precomp a T) (precomp b T)) b ≫
        internalHom.homEquiv W T (pullback (precomp a T) (precomp b T))
          (pullback.snd (precomp a T) (precomp b T)) := sorry

/-- The copower cocone represented by the canonical internal-hom pullback projections. This is
the canonical-representation specialization of `comparisonOf.inv.cocone`. -/
@[stacks 017N "cocone defining the inverse internal-hom pushout comparison"]
def cocone : PushoutCocone
    (copower.indexHom (pullback (precomp a T) (precomp b T)) a)
    (copower.indexHom (pullback (precomp a T) (precomp b T)) b) :=
  comparisonOf.inv.cocone a b (internalHom.representableBy U T)
    (internalHom.representableBy V T) (internalHom.representableBy W T)

end inv

/-- The inverse comparison from the internal-hom pullback to the internal mapping object out
of the simplicial-set pushout. This is the canonical-representation specialization of the
explicit inverse. -/
@[stacks 017N "inverse internal-hom pushout comparison"]
def inv :
    pullback (precomp a T) (precomp b T) ⟶ internalHom (pushout a b) T :=
  comparisonOf.inv a b (internalHom.representableBy U T)
    (internalHom.representableBy V T) (internalHom.representableBy W T)
    (internalHom.representableBy (pushout a b) T)

/-- Under the representing equivalence, the inverse comparison is the explicit descent map
out of the pushout-indexed copower. -/
@[stacks 017N "representation formula for the inverse internal-hom pushout comparison"]
theorem inv.homEquiv :
    internalHom.homEquiv (pushout a b) T
        (pullback (precomp a T) (precomp b T)) (inv a b T) =
      copower.pushout.desc.hom a b (pullback (precomp a T) (precomp b T))
        (inv.cocone a b T) := sorry

/-- The pushout comparison followed by its explicitly constructed inverse is the identity. -/
@[stacks 017N "forward-inverse law for the internal-hom pushout comparison"]
theorem hom_inv_id : pushout.comparison a b T ≫ inv a b T = 𝟙 _ := sorry

/-- The explicitly constructed inverse followed by the pushout comparison is the identity. -/
@[stacks 017N "inverse-forward law for the internal-hom pushout comparison"]
theorem inv_hom_id : inv a b T ≫ pushout.comparison a b T = 𝟙 _ := sorry

/-- The internal mapping object out of a simplicial-set pushout is explicitly isomorphic to
the pullback of the two precomposition maps. This is the canonical-representation specialization
of `comparisonOf.iso`. -/
@[stacks 017N "internal hom out of a pushout as a pullback"]
def iso :
    internalHom (pushout a b) T ≅ pullback (precomp a T) (precomp b T) :=
  comparisonOf.iso a b (internalHom.representableBy U T)
    (internalHom.representableBy V T) (internalHom.representableBy W T)
    (internalHom.representableBy (pushout a b) T)

/-- The comparison between chosen internal-hom representations sends a simplicial-set pushout
to the corresponding pullback. -/
@[stacks 017N, instance]
theorem isIso : IsIso (pushout.comparison a b T) := sorry

end comparison

end CategoryTheory.SimplicialObject.internalHom.pushout
