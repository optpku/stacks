module

public import stacks_project.Chap60.Remark_60_9_4_Comparison_with_Zariski_site_Comparison
import StacksCheckRecall

/- Remark 60.9.4 (Comparison with Zariski site) (1): the small crystalline
   forgetful functor is continuous. -/
@[stacks 07IL] #check @AlgebraicGeometry.Scheme.Crystalline.forgetfulFunctor_isContinuous

/- Remark 60.9.4 (Comparison with Zariski site) (2): the small crystalline
   forgetful functor is cocontinuous. -/
@[stacks 07IL] #check @AlgebraicGeometry.Scheme.Crystalline.forgetfulFunctor_isCocontinuous

/- Remark 60.9.4 (Comparison with Zariski site) (3): the forgetful functor
   preserves products and fibre products via finite nonempty limits. -/
@[stacks 07IL] #check @AlgebraicGeometry.Scheme.Crystalline.forgetfulFunctor_preservesFiniteNonemptyLimits

/- Remark 60.9.4 (Comparison with Zariski site) (4): these properties induce
   the canonical morphism from the small crystalline topos to the small Zariski topos. -/
@[stacks 07IL] #check @AlgebraicGeometry.Scheme.Crystalline.smallCrystallineToposMorphism
