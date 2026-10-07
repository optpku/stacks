module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Locality

/-!
# Stalkwise universal catenarity

A criterion for universal catenarity of a locally Noetherian scheme in terms of its stalk
rings, together with its two directions and the canonical stalk instance.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A locally Noetherian scheme is universally catenary exactly when all of its stalk rings
are universally catenary. -/
theorem UniversallyCatenary.iff_forall_stalk (S : Scheme.{u}) [IsLocallyNoetherian S] :
    UniversallyCatenary S ↔
      ∀ s : S, UniversallyCatenaryRing.{u, u} (S.presheaf.stalk s) := sorry

/-- The stalk ring at every point of a universally catenary scheme is canonically universally
catenary. -/
instance instUniversallyCatenaryRingStalk (S : Scheme.{u}) [UniversallyCatenary S] (s : S) :
    UniversallyCatenaryRing.{u, u} (S.presheaf.stalk s) :=
  (UniversallyCatenary.iff_forall_stalk S).1
    (inferInstance : UniversallyCatenary S) s

/-- Every stalk ring of a universally catenary scheme is universally catenary. -/
theorem UniversallyCatenary.stalk_universallyCatenaryRing {S : Scheme.{u}}
    (hS : UniversallyCatenary S) (s : S) :
    UniversallyCatenaryRing.{u, u} (S.presheaf.stalk s) :=
  @instUniversallyCatenaryRingStalk S hS s

/-- A locally Noetherian scheme whose stalk rings are all universally catenary is universally
catenary. -/
theorem universallyCatenary_of_forall_stalk_universallyCatenaryRing
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (hS : ∀ s : S, UniversallyCatenaryRing.{u, u} (S.presheaf.stalk s)) :
    UniversallyCatenary S :=
  (UniversallyCatenary.iff_forall_stalk S).2 hS

end AlgebraicGeometry
