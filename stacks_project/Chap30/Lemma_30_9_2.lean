module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
import Mathlib.AlgebraicGeometry.Noetherian
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/- Lemma 30.9.2 (01Y0) (1): the kernel of a morphism between coherent modules on a locally
Noetherian scheme is coherent. -/
@[stacks 01Y0 "(1)"]
#check (SheafOfModules.IsCoherent.kernel :
  ∀ {F G : X.toRingedSpace.Modules} (f : F ⟶ G) [F.IsCoherent] [G.IsCoherent],
    (kernel f).IsCoherent)

/- Lemma 30.9.2 (01Y0) (2): the cokernel of a morphism between coherent modules on a locally
Noetherian scheme is coherent. -/
@[stacks 01Y0 "(2)"]
#check (SheafOfModules.IsCoherent.cokernel :
  ∀ {F G : X.toRingedSpace.Modules} (f : F ⟶ G) [F.IsCoherent] [G.IsCoherent],
    (cokernel f).IsCoherent)

/- Lemma 30.9.2 (01Y0) (3): in a short exact sequence of modules on a locally Noetherian
scheme, coherence of the outer terms implies coherence of the middle term. -/
@[stacks 01Y0 "(3)"]
#check (SheafOfModules.IsCoherent.middle_of_shortExact :
  ∀ {S : ShortComplex X.toRingedSpace.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₃.IsCoherent], S.X₂.IsCoherent)

/- Lemma 30.9.2 (01Y0) (4): coherent modules on a locally Noetherian scheme form an abelian
category. -/
@[stacks 01Y0 "(4)"]
#check
  (CategoryTheory.ObjectProperty.instAbelianFullSubcategoryOfContainsZeroOfIsClosedUnderKernelsOfIsClosedUnderCokernelsOfIsClosedUnderFiniteProducts
    (P := SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) :
      Abelian (RingedSpace.Coh X.toRingedSpace))

end AlgebraicGeometry.Scheme.Modules
