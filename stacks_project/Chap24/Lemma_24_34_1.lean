module

public import ReasLib.AlgebraicGeometry.RingedSite.DifferentialGraded.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

/-!
# Restriction to a cofiltered full subcategory

Restriction of the structure sheaf, DGA, and DG modules is owned by the reusable chaotic-site
restriction API.  The cofiltered category `U / C'` is represented by
`StructuredArrow U P.ι`; its hypothesis makes the inclusion representably flat.  The remaining
0GZE work is the derived localization and proof that restriction and extension preserve and are
quasi-inverse on the quasi-coherent loci.
-/

section

variable {C : Type u} [Category.{v} C]
variable (P : ObjectProperty C)
variable [∀ U : C, IsCofiltered (StructuredArrow U P.ι)]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{w})
variable (A : DGA(O))

/- Lemma 24.34.1 (tag 0GZE), restriction-side owner: the source hypothesis supplies the
actual restriction functor on DG modules over the restricted DGA.  Its derived QC equivalence
is pending. -/
@[stacks 0GZE "DG-module restriction; derived QC equivalence pending"]
#check
  (RingedSite.Chaotic.restrictDGModule P.ι O A)

/- The same hypothesis supplies the representable-flatness required by the ringed-site owner. -/
#check (ObjectProperty.representablyFlat_ι P : RepresentablyFlat P.ι)

/- The structure sheaf and coefficient DGA are restricted by canonical direct-image functors. -/
#check (RingedSite.Chaotic.restrictSheaf P.ι O)
#check (RingedSite.Chaotic.restrictDGA P.ι O)

/- The extension side is present at the underived DG-module level as the canonical left adjoint
of restriction.  Its identification with the displayed pointwise filtered-colimit formula belongs
to the remaining derived QC comparison. -/
#check (RingedSite.Chaotic.extendDGModule P.ι O A)
#check (RingedSite.Chaotic.dgModuleAdjunction P.ι O A)

end
