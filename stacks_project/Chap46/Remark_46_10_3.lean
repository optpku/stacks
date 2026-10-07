module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.DerivedAdeq.Localization

open CategoryTheory
open AlgebraicGeometry

/- Remark 46.10.3: derived Zariski restriction identifies the Verdier quotient of
`DerivedAdeq S τ` by the objects with parasitic cohomology with `Scheme.DerivedQCoh S`. -/
@[stacks 070X] #check
  (SheafOfModules.DerivedAdeq.Parasitic.equivalence :
    (S : Scheme) → (τ : StandardTopology) →
      ObjectProperty.verdierQuotient
          (SheafOfModules.DerivedAdeq.Parasitic.property S τ) ≌
        Scheme.DerivedQCoh S)
