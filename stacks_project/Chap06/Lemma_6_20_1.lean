module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- The installed module-sheafification API separates the source's construction into its canonical
data owner `PresheafOfModules.sheafification`, the theorem identifying the underlying additive
unit, and the adjunction owning the factorization property. Recalling these three surfaces keeps
the scalar multiplication and comparison morphism explicit, avoids a duplicate existential
wrapper, and gives downstream users both the source diagram and its reusable universal property. -/

/- Lemma 6.20.1 (1): sheafifying a presheaf of modules along a locally bijective map from the
ring presheaf to a sheaf of rings canonically produces the associated sheaf of modules. -/
@[stacks 0089 "module structure on the additive sheafification"]
recall PresheafOfModules.sheafification

/- Lemma 6.20.1 (2): after forgetting module structures, the unit of module sheafification is the
ordinary sheafification map of the underlying presheaf of abelian groups, which is the commuting
square in the source. -/
@[stacks 0089 "compatibility of the module and additive sheafification maps"]
recall PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app

/- Lemma 6.20.1 (3): module sheafification is left adjoint to forgetting a sheaf of modules and
restricting scalars, giving the unique factorization through the canonical sheafification map. -/
@[stacks 0089 "unique factorization into a sheaf of modules"]
recall PresheafOfModules.sheafificationAdjunction
