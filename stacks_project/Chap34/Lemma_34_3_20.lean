module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SheafData

universe u

/- Lemma 34.3.20: a sheaf on the big Zariski site over `S` is equivalently
specified by compatible sheaves on every scheme over `S`, with inverse-image
maps that are isomorphisms along open immersions. -/
@[stacks 0213] #check (AlgebraicGeometry.Scheme.Zariski.Big.sheafDataEquivalence :
    (S : AlgebraicGeometry.Scheme.{u}) →
      AlgebraicGeometry.Scheme.Zariski.Big.SheafDataEquivalence S)
