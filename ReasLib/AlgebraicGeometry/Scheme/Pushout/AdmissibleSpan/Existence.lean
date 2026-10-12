/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.StructureSheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan

/-- An admissible span of schemes over a fixed base has a pushout in the category of
schemes. -/
instance instHasPushout {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    HasPushout i.left j.left := sorry

/-- The canonical pushout square of an admissible span is also a pullback square. -/
theorem isPullback {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    IsPullback i.left j.left (pushout.inl i.left j.left) (pushout.inr i.left j.left) := sorry

/-- The canonical morphism from the first target of an admissible span to its pushout is
integral. -/
instance instInlIsIntegralHom {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    IsIntegralHom (pushout.inl i.left j.left) := sorry

/-- The canonical morphism from the second target of an admissible span to its pushout is
a closed immersion. -/
instance instInrIsClosedImmersion {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    IsClosedImmersion (pushout.inr i.left j.left) := sorry

/-- The structure sheaf on the pushout of an admissible span is the sectionwise pullback
of the pushed-forward structure sheaves on its three other vertices. -/
theorem structureSheaf_isPullback {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    IsStructureSheafPullback (IsPushout.of_hasPushout i.left j.left).toCommSq := sorry

end AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan
