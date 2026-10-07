module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType.FilteredColimit
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 17.9.7 (01BB) (1): a finite-type directed colimit on a quasi-compact ringed space is
the quotient of one stage through its canonical colimit map. -/
@[stacks 01BB "(1)"]
#check fun {X : RingedSpace.{u}} [CompactSpace X]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ X.Modules) [(colimit F).IsFiniteType] ↦
  SheafOfModules.IsFiniteType.FilteredColimit.exists_epi_ι
    (𝒪 := X.ringCatSheaf) F

/- Lemma 17.9.7 (01BB) (2): if all transition maps are mono, the finite-type colimit is
canonically isomorphic to one stage. -/
@[stacks 01BB "(2)"]
#check fun {X : RingedSpace.{u}} [CompactSpace X]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ X.Modules) [(colimit F).IsFiniteType]
    [∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f)] ↦
  SheafOfModules.IsFiniteType.FilteredColimit.exists_isIso_ι
    (𝒪 := X.ringCatSheaf) F
