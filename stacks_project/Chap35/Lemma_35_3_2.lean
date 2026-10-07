module

public import ReasLib.Algebra.Module.DescentDatum.Cosimplicial
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.3.2: a module descent datum determines a module over the Amitsur
cosimplicial ring, with the stated degree and map formulas, functorially in the
descent datum. -/
@[stacks 023H] #check (Module.DescentDatum.cosimplicial :
  ∀ {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [SMulCommClass R A N],
    Module.DescentDatum R A N → Algebra.Amitsur.CosimplicialModule R A)

#check Module.DescentDatum.cosimplicial_obj
#check Module.DescentDatum.cosimplicial_map
#check Module.DescentDatum.Hom.cosimplicial
#check Module.DescentDatum.Hom.cosimplicial_app
#check Module.DescentDatum.Hom.cosimplicial_id
#check Module.DescentDatum.Hom.cosimplicial_comp
