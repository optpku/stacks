module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction
public import stacks_project.Chap85.Lemma_85_28_3_Pullback
public import stacks_project.Chap85.Lemma_85_28_3_Pushforward

/-!
# Lemma 85.28.3

The pullback-pushforward adjunction for quasi-coherent modules along a
cartesian morphism of simplicial schemes with flat cofaces and quasi-compact
quasi-separated components.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty Opposite RingedSite
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- Lemma 85.28.3: let `f : V ⟶ U` be a cartesian morphism of simplicial schemes.
Assume the coface morphisms `U.δ j : U _⦋n+1⦌ ⟶ U _⦋n⦌` are flat and the
component morphisms `f.app (op ⦋n⦌) : V _⦋n⦌ ⟶ U _⦋n⦌` are quasi-compact and
quasi-separated. Then `QCoh.pullback f : QCoh U ⥤ QCoh V` and
`QCoh.pushforward f : QCoh V ⥤ QCoh U` form an adjoint pair of functors
between the categories of quasi-coherent modules on `zariskiRingedSite U`
and `zariskiRingedSite V`. -/
@[stacks 07TK]
noncomputable def QCoh.pullbackPushforwardAdjunction
    {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    [CategoryTheory.SimplicialObject.IsCartesian f]
    [∀ (n : ℕ) (j : Fin (n + 2)), Flat (U.δ j)]
    [∀ (n : ℕ), QuasiCompact (f.app (op ⦋n⦌))]
    [∀ (n : ℕ), QuasiSeparated (f.app (op ⦋n⦌))] :
    (QCoh.pullback f : QCoh U ⥤ QCoh V) ⊣
      (QCoh.pushforward f : QCoh V ⥤ QCoh U) :=
  ObjectProperty.FullSubcategory.adjunction (modulePullback f)
    ((zariskiRingedHom f).modulePushforward.{u})
    (Hom.modulePullbackPushforwardAdjunction (zariskiRingedHom f))
    (QCoh.pullback.mapsTo f) (QCoh.pushforward.mapsTo f)

end AlgebraicGeometry.SimplicialObject
