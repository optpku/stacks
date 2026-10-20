module

public import ReasLib.Algebra.Category.Ring.KanExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose

/-!
# Universe-lifted structure sheaves on standard scheme sites

This module gives an explicit universe lift for ring-valued sheaves and applies it to the
standard big, small étale, and small Zariski structure sheaves and ringed sites.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe uX vX w l

namespace AlgebraicGeometry.Scheme.Site

/-- Lift a bundled ring to a larger universe while retaining its operations explicitly. -/
noncomputable def ringUniverseLiftObj (R : RingCat.{w}) : RingCat.{max w l} :=
  RingCat.of (ULift.{l} R)

/-- Lift a bundled ring homomorphism between explicit universe lifts. -/
noncomputable def ringUniverseLiftMap {R S : RingCat.{w}} (f : R ⟶ S) :
    ringUniverseLiftObj.{w, l} R ⟶ ringUniverseLiftObj.{w, l} S :=
  RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    (f.hom.comp ULift.ringEquiv.toRingHom))

/-- Universe lifting preserves identity ring homomorphisms. -/
theorem ringUniverseLiftMap_id (R : RingCat.{w}) :
    ringUniverseLiftMap.{w, l} (𝟙 R) = 𝟙 (ringUniverseLiftObj.{w, l} R) := sorry

/-- Universe lifting preserves composition of ring homomorphisms. -/
theorem ringUniverseLiftMap_comp {R S T : RingCat.{w}} (f : R ⟶ S) (g : S ⟶ T) :
    ringUniverseLiftMap.{w, l} (f ≫ g) =
      ringUniverseLiftMap.{w, l} f ≫ ringUniverseLiftMap.{w, l} g := sorry

/-- The functor embedding rings into a larger universe by `ULift`. -/
noncomputable def ringUniverseLift : RingCat.{w} ⥤ RingCat.{max w l} where
  obj := ringUniverseLiftObj
  map := ringUniverseLiftMap
  map_id := ringUniverseLiftMap_id
  map_comp := ringUniverseLiftMap_comp

/-- The universe-lift functor acts on objects by the explicit lifted ring. -/
theorem ringUniverseLift_obj (R : RingCat.{w}) :
    (ringUniverseLift.{w, l}).obj R = ringUniverseLiftObj.{w, l} R := sorry

/-- Universe lifting of rings is compatible with forming sheaves. -/
instance ringUniverseLift_hasSheafCompose
    {C : Type uX} [Category.{vX} C] (J : GrothendieckTopology C) :
    J.HasSheafCompose (ringUniverseLift.{w, l}) := sorry

end AlgebraicGeometry.Scheme.Site

namespace AlgebraicGeometry.StandardTopology.Big

universe u

/-- The standard big-site structure sheaf with section rings lifted to the site universe. -/
noncomputable def liftedStructureSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Sheaf (τ.overTopology S) RingCat.{u + 1} :=
  (sheafCompose (τ.overTopology S) (Scheme.Site.ringUniverseLift.{u, u + 1})).obj
    (structureSheaf τ S)

/-- The lifted big-site structure sheaf is obtained by universe-lifting every section ring. -/
theorem liftedStructureSheaf_def (τ : StandardTopology) (S : Scheme.{u}) :
    liftedStructureSheaf τ S =
      (sheafCompose (τ.overTopology S)
        (Scheme.Site.ringUniverseLift.{u, u + 1})).obj (structureSheaf τ S) := sorry

/-- The standard big site equipped with its universe-lifted structure sheaf. -/
abbrev liftedRingedSite (τ : StandardTopology) (S : Scheme.{u}) :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf (τ.overTopology S) (liftedStructureSheaf τ S)

/-- The lifted big ringed site's structure sheaf is the lifted global-sections sheaf. -/
theorem liftedRingedSite_structureSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    (liftedRingedSite τ S).structureSheaf = liftedStructureSheaf τ S := sorry

end AlgebraicGeometry.StandardTopology.Big

namespace AlgebraicGeometry.Scheme.Etale.Small

universe u

/-- The small étale structure sheaf with section rings lifted to the site universe. -/
noncomputable def liftedStructureSheaf (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology RingCat.{u + 1} :=
  (sheafCompose T.smallEtaleTopology
    (Scheme.Site.ringUniverseLift.{u, u + 1})).obj (structureSheaf T)

/-- The lifted small-étale structure sheaf universe-lifts every section ring. -/
theorem liftedStructureSheaf_def (T : Scheme.{u}) :
    liftedStructureSheaf T =
      (sheafCompose T.smallEtaleTopology
        (Scheme.Site.ringUniverseLift.{u, u + 1})).obj (structureSheaf T) := sorry

/-- The small étale site equipped with its universe-lifted structure sheaf. -/
abbrev liftedRingedSite (T : Scheme.{u}) : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf T.smallEtaleTopology (liftedStructureSheaf T)

/-- The lifted small-étale ringed site's structure sheaf is the lifted global-sections sheaf. -/
theorem liftedRingedSite_structureSheaf (T : Scheme.{u}) :
    (liftedRingedSite T).structureSheaf = liftedStructureSheaf T := sorry

end AlgebraicGeometry.Scheme.Etale.Small

namespace AlgebraicGeometry.Scheme.Zariski.Small

universe u

/-- The small Zariski structure sheaf with section rings lifted to the site universe. -/
noncomputable def liftedStructureSheaf (T : Scheme.{u}) :
    Sheaf T.smallZariskiTopology RingCat.{u + 1} :=
  (sheafCompose T.smallZariskiTopology
    (Scheme.Site.ringUniverseLift.{u, u + 1})).obj (structureSheaf T)

/-- The lifted small-Zariski structure sheaf universe-lifts every section ring. -/
theorem liftedStructureSheaf_def (T : Scheme.{u}) :
    liftedStructureSheaf T =
      (sheafCompose T.smallZariskiTopology
        (Scheme.Site.ringUniverseLift.{u, u + 1})).obj (structureSheaf T) := sorry

/-- The small Zariski site equipped with its universe-lifted structure sheaf. -/
abbrev liftedRingedSite (T : Scheme.{u}) : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf T.smallZariskiTopology (liftedStructureSheaf T)

/-- The lifted small-Zariski ringed site's structure sheaf is the lifted global-sections sheaf. -/
theorem liftedRingedSite_structureSheaf (T : Scheme.{u}) :
    (liftedRingedSite T).structureSheaf = liftedStructureSheaf T := sorry

end AlgebraicGeometry.Scheme.Zariski.Small
