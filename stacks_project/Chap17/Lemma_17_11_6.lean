module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.FinitePresentation
import StacksCheckRecall

/-!
# Lemma 17.11.6

The associated-module functor preserves filtered colimits and sends finitely presented modules
to finitely presented module sheaves.  The source theorem is therefore a direct specialization of
the shared associated-sheaf API.
-/

@[expose] public section

open CategoryTheory.ObjectProperty AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Associated

variable {X : RingedSpace.{u}}
variable (M : ModuleCat.{u} X.globalSectionsRing)

/- Lemma 17.11.6 (01BR): the module sheaf associated to `M` is a filtered colimit of finitely
presented `𝒪_X`-modules. -/
@[stacks 01BR]
#check
  (ind_obj (RingHom.id X.globalSectionsRing) M :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).ind.{u}
      (Associated.obj (RingHom.id X.globalSectionsRing) M))

end AlgebraicGeometry.RingedSpace.Module.Associated
