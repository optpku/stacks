/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Map

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

variable {X Y S T : Scheme.{u}}

/-- The canonical set-valued étale base-change comparison is an isomorphism if its
comparisons over an étale cover with étale factorizations are isomorphisms. -/
theorem setMap_isIso_of_cover
    (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (h_cart : IsPullback h e f g) (𝒰 : X.Cover Scheme.etalePrecoverage)
    (V : 𝒰.I₀ → Scheme.{u})
    (fi : ∀ i, 𝒰.X i ⟶ V i) (vi : ∀ i, V i ⟶ S)
    (h_factor : ∀ i, 𝒰.f i ≫ f = fi i ≫ vi i)
    (h_V_etale : ∀ i, Etale (vi i)) (P Q : 𝒰.I₀ → Scheme.{u})
    (hi : ∀ i, P i ⟶ 𝒰.X i) (piY : ∀ i, P i ⟶ Y)
    (ei : ∀ i, P i ⟶ Q i) (gi : ∀ i, Q i ⟶ V i) (ti : ∀ i, Q i ⟶ T)
    (h_P : ∀ i, IsPullback (hi i) (piY i) (𝒰.f i) h)
    (h_Q : ∀ i, IsPullback (gi i) (ti i) (vi i) g)
    (h_local : ∀ i, IsPullback (hi i) (ei i) (fi i) (gi i))
    (h_T : ∀ i, piY i ≫ e = ei i ≫ ti i)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (h_local_iso : ∀ i, IsIso (setMap (fi i) (hi i) (ei i) (gi i) (h_local i)
      (((Scheme.smallEtalePullback (ti i)).sheafPullback (Type (u + 1))
        T.smallEtaleTopology (Q i).smallEtaleTopology).obj F))) :
    IsIso (setMap f h e g h_cart F) := sorry

/-- The canonical base-change comparison on the unbounded derived category of
abelian étale sheaves is an isomorphism if its comparisons over an étale cover
with étale factorizations are isomorphisms. -/
theorem derivedMap_isIso_of_cover
    (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (h_cart : IsPullback h e f g) (𝒰 : X.Cover Scheme.etalePrecoverage)
    (V : 𝒰.I₀ → Scheme.{u})
    (fi : ∀ i, 𝒰.X i ⟶ V i) (vi : ∀ i, V i ⟶ S)
    (h_factor : ∀ i, 𝒰.f i ≫ f = fi i ≫ vi i)
    (h_V_etale : ∀ i, Etale (vi i)) (P Q : 𝒰.I₀ → Scheme.{u})
    (hi : ∀ i, P i ⟶ 𝒰.X i) (piY : ∀ i, P i ⟶ Y)
    (ei : ∀ i, P i ⟶ Q i) (gi : ∀ i, Q i ⟶ V i) (ti : ∀ i, Q i ⟶ T)
    (h_P : ∀ i, IsPullback (hi i) (piY i) (𝒰.f i) h)
    (h_Q : ∀ i, IsPullback (gi i) (ti i) (vi i) g)
    (h_local : ∀ i, IsPullback (hi i) (ei i) (fi i) (gi i))
    (h_T : ∀ i, piY i ≫ e = ei i ≫ ti i)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (h_local_iso : ∀ i, IsIso (derivedMap (fi i) (hi i) (ei i) (gi i) (h_local i)
      ((Derived.inverseImage (ti i)).obj K))) :
    IsIso (derivedMap f h e g h_cart K) := sorry

/-- The canonical degree-`q` higher-direct-image base-change comparison for an
abelian étale sheaf is an isomorphism if its degree-`q` comparisons over an
étale cover with étale factorizations are isomorphisms. -/
theorem higherMap_isIso_of_cover
    (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (h_cart : IsPullback h e f g) (𝒰 : X.Cover Scheme.etalePrecoverage)
    (V : 𝒰.I₀ → Scheme.{u})
    (fi : ∀ i, 𝒰.X i ⟶ V i) (vi : ∀ i, V i ⟶ S)
    (h_factor : ∀ i, 𝒰.f i ≫ f = fi i ≫ vi i)
    (h_V_etale : ∀ i, Etale (vi i)) (P Q : 𝒰.I₀ → Scheme.{u})
    (hi : ∀ i, P i ⟶ 𝒰.X i) (piY : ∀ i, P i ⟶ Y)
    (ei : ∀ i, P i ⟶ Q i) (gi : ∀ i, Q i ⟶ V i) (ti : ∀ i, Q i ⟶ T)
    (h_P : ∀ i, IsPullback (hi i) (piY i) (𝒰.f i) h)
    (h_Q : ∀ i, IsPullback (gi i) (ti i) (vi i) g)
    (h_local : ∀ i, IsPullback (hi i) (ei i) (fi i) (gi i))
    (h_T : ∀ i, piY i ≫ e = ei i ≫ ti i)
    (q : ℕ) (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h_local_iso : ∀ i, IsIso (higherMap (fi i) (hi i) (ei i) (gi i) (h_local i) q
      ((Abelian.inverseImage (ti i)).obj F))) :
    IsIso (higherMap f h e g h_cart q F) := sorry

end AlgebraicGeometry.Scheme.Etale.BaseChange
