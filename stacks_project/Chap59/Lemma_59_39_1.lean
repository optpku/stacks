module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/-- The identity object of the small étale site of a scheme. -/
abbrev globalEtale (X : Scheme.{u}) : X.Etale :=
  AlgebraicGeometry.Scheme.Etale.globalEtale X

/-- Base change of the identity étale object along a scheme morphism is the identity étale object of
the domain. -/
noncomputable abbrev globalEtalePullbackIso {S T : Scheme.{u}} (f : T ⟶ S) :
    (smallEtalePullback f).obj (globalEtale S) ≅ globalEtale T :=
  AlgebraicGeometry.Scheme.Etale.globalEtalePullbackIso f

/-- Restriction of a global étale section along a scheme morphism by pullback along the small étale
site functor. -/
noncomputable abbrev restrictGlobalSection {S T : Scheme.{u}} (f : T ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (σ : F.obj.obj (op (globalEtale S))) :
    (((smallEtalePullback f).sheafPullback (Type (u + 1))
        S.smallEtaleTopology T.smallEtaleTopology).obj F).obj.obj
      (op (globalEtale T)) :=
  AlgebraicGeometry.Scheme.Etale.restrictGlobalSection f F σ

/- Lemma 59.39.1 -/
@[stacks 09XM] #check
  (AlgebraicGeometry.Scheme.Etale.existsUnique_open_of_eq_sections :
    ∀ {S : Scheme.{u}}
      (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
      (s t : F.obj.obj (op (AlgebraicGeometry.Scheme.Etale.globalEtale S))),
      ∃! W : S.Opens,
        ∀ {T : Scheme.{u}} (f : T ⟶ S),
          (∃ g : T ⟶ W, g ≫ W.ι = f) ↔
            AlgebraicGeometry.Scheme.Etale.restrictGlobalSection f F s =
              AlgebraicGeometry.Scheme.Etale.restrictGlobalSection f F t)
