module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Tangent.RightExact
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 46.4.7 (1): in a pointwise short exact sequence of module-valued functors,
condition `(*)` passes from the first two terms to the third. -/
@[stacks 06ZF] #check
  (ModuleValuedFunctor.TangentRightExact.of_pointwiseShortExact_left_middle :
    ∀ {A : CommRingCat.{u}} {F G H : ModuleValuedFunctor.{u, u} A}
      (f : ModuleValuedFunctor.Hom F G) (g : ModuleValuedFunctor.Hom G H),
      f.IsPointwiseShortExact g → ModuleValuedFunctor.TangentRightExact F →
        ModuleValuedFunctor.TangentRightExact G → ModuleValuedFunctor.TangentRightExact H)

/- Lemma 46.4.7 (2): in a pointwise short exact sequence of module-valued functors,
condition `(*)` passes from the outer terms to the middle term. -/
@[stacks 06ZF] #check
  (ModuleValuedFunctor.TangentRightExact.of_pointwiseShortExact_ends :
    ∀ {A : CommRingCat.{u}} {F G H : ModuleValuedFunctor.{u, u} A}
      (f : ModuleValuedFunctor.Hom F G) (g : ModuleValuedFunctor.Hom G H),
      f.IsPointwiseShortExact g → ModuleValuedFunctor.TangentRightExact F →
        ModuleValuedFunctor.TangentRightExact H → ModuleValuedFunctor.TangentRightExact G)

/- Lemma 46.4.7 (3): if all four module-valued functors satisfy condition `(*)`, then
so does the pointwise pullback of the middle term along a morphism to the last term. -/
@[stacks 06ZF] #check
  (ModuleValuedFunctor.TangentRightExact.pullback_of_pointwiseShortExact :
    ∀ {A : CommRingCat.{u}} {F G H H' : ModuleValuedFunctor.{u, u} A}
      (f : ModuleValuedFunctor.Hom F G) (g : ModuleValuedFunctor.Hom G H),
      f.IsPointwiseShortExact g → ∀ (α : ModuleValuedFunctor.Hom H' H),
        ModuleValuedFunctor.TangentRightExact F →
          ModuleValuedFunctor.TangentRightExact G →
            ModuleValuedFunctor.TangentRightExact H →
              ModuleValuedFunctor.TangentRightExact H' →
                ModuleValuedFunctor.TangentRightExact (ModuleValuedFunctor.pullback g α))
