module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.Scheme.Module.PullbackSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace

/-!
# The twisting sheaf `𝒪(1)` on projective space over an algebraic space

The sheaf `𝒪_{P^n_Y}(1)` is the pullback of the étale transfer of the scheme-level
`𝒪_{P^n_S}(1)`, itself the pullback of the standard twisting sheaf on `P^n_ℤ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme-level sheaf `𝒪_{P^n_S}(1)`, obtained by pulling back the standard twisting
sheaf on `P^n` over `ℤ`. -/
def twistingSheafScheme (n : ℕ) (S : Scheme.{u}) :
    (AlgebraicGeometry.ProjectiveSpace n S).Modules :=
  (Scheme.Modules.pullback
      (pullback.snd (terminal.from S)
        (terminal.from (AlgebraicGeometry.ProjectiveSpace.scheme (ULift.{u} ℤ) n)))).obj
    (AlgebraicGeometry.ProjectiveSpace.twistingSheaf (ULift.{u} ℤ) n 1)

/-- The structure morphism of an étale object over `ofScheme n S` as a morphism of schemes
into `P^n_S`. -/
def twistingSheafSchemeHom (n : ℕ) (S : Scheme.{u})
    (U : smallEtaleSite (ofScheme n S)) :
    U.left.left ⟶ AlgebraicGeometry.ProjectiveSpace n S :=
  (Yoneda.fullyFaithful.preimage
    (U.hom : yoneda.obj U.left ⟶
      yoneda.obj (Over.mk (AlgebraicGeometry.ProjectiveSpace.toBase n S)))).left

/-- A morphism of étale objects over `ofScheme n S` is compatible with the structure
morphisms to `P^n_S`. -/
theorem twistingSheafSchemeHom_comp (n : ℕ) (S : Scheme.{u})
    {U V : smallEtaleSite (ofScheme n S)} (f : U ⟶ V) :
    f.left.left ≫ twistingSheafSchemeHom n S V = twistingSheafSchemeHom n S U :=
  sorry

/-- The functor sending an étale chart of represented projective space to its structure
morphism into the representing scheme. -/
def ofSchemeEtaleToOver (n : ℕ) (S : Scheme.{u}) :
    smallEtaleSite (ofScheme n S) ⥤
      CategoryTheory.Over (AlgebraicGeometry.ProjectiveSpace n S) :=
  (smallEtaleToScheme (ofScheme n S)).toOver
    (AlgebraicGeometry.ProjectiveSpace n S) (twistingSheafSchemeHom n S)
    (twistingSheafSchemeHom_comp n S)

/-- The étale transfer of `𝒪_{P^n_S}(1)` as a presheaf of modules over the small-étale
structure sheaf of `ofScheme n S`. -/
def twistingSheafOfSchemePresheaf (n : ℕ) (S : Scheme.{u}) :
    PresheafOfModules (structureSheaf (ofScheme n S)).obj :=
  Scheme.Modules.PullbackSections.modulePresheaf
    (ofSchemeEtaleToOver n S) (twistingSheafScheme n S)

/-- At an étale object `U`, the transferred sheaf has value the global sections of the
pullback of `𝒪_{P^n_S}(1)` along the structure morphism of `U`. -/
theorem twistingSheafOfSchemePresheaf_obj (n : ℕ) (S : Scheme.{u})
    (U : (smallEtaleSite (ofScheme n S))ᵒᵖ) :
    (twistingSheafOfSchemePresheaf n S).obj U =
      Scheme.Modules.PullbackSections.moduleObj
        (ofSchemeEtaleToOver n S) (twistingSheafScheme n S) U :=
  rfl

/-- Restriction in the étale transfer of `𝒪_{P^n_S}(1)` is the canonical pullback-sections
map over the small-étale structure sheaf. -/
theorem twistingSheafOfSchemePresheaf_map (n : ℕ) (S : Scheme.{u})
    {U V : (smallEtaleSite (ofScheme n S))ᵒᵖ} (i : U ⟶ V) :
    (twistingSheafOfSchemePresheaf n S).map i =
      Scheme.Modules.PullbackSections.moduleMap
        (ofSchemeEtaleToOver n S) (twistingSheafScheme n S) i :=
  rfl

/-- The étale transfer of `𝒪_{P^n_S}(1)` satisfies the sheaf condition. -/
theorem twistingSheafOfSchemePresheaf_isSheaf (n : ℕ) (S : Scheme.{u}) :
    Presheaf.IsSheaf (smallEtaleTopology (ofScheme n S))
      (twistingSheafOfSchemePresheaf n S).presheaf :=
  sorry

/-- The sheaf `𝒪_{P^n_S}(1)` on `ofScheme n S`. -/
def twistingSheafOfScheme (n : ℕ) (S : Scheme.{u}) : (ofScheme n S).Modules where
  val := twistingSheafOfSchemePresheaf n S
  isSheaf := twistingSheafOfSchemePresheaf_isSheaf n S

/-- The underlying presheaf of `twistingSheafOfScheme n S` is the pullback-sections
presheaf of `𝒪_{P^n_S}(1)` over the small-étale structure sheaf. -/
theorem twistingSheafOfScheme_val (n : ℕ) (S : Scheme.{u}) :
    (twistingSheafOfScheme n S).val = twistingSheafOfSchemePresheaf n S :=
  rfl

namespace ProjectiveSpace

/-- The twisting sheaf `𝒪_{P^n_Y}(1)` on projective space over an algebraic space. -/
def twistingSheaf (n : ℕ) {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    (ProjectiveSpace n Y).Modules :=
  (Modules.pullback (toOfScheme n Y)).obj (twistingSheafOfScheme n S)

/-- `twistingSheaf n Y` is the module pullback of `𝒪_{P^n_S}(1)` along `toOfScheme`. -/
theorem twistingSheaf_spec (n : ℕ) {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    twistingSheaf n Y =
      (Modules.pullback (toOfScheme n Y)).obj (twistingSheafOfScheme n S) :=
  rfl

/-- The twisting sheaf `𝒪_{P^n_Y}(1)` is invertible. -/
instance twistingSheaf_isInvertible (n : ℕ) {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    isInvertibleObject (twistingSheaf n Y) :=
  sorry

/-- The pullback of `𝒪_{P^n_Y}(1)` along a morphism into projective space is invertible. -/
instance pullback_twistingSheaf_isInvertible {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (n : ℕ) (i : X ⟶ ProjectiveSpace n Y) :
    isInvertibleObject ((Modules.pullback i).obj (twistingSheaf n Y)) :=
  sorry

end ProjectiveSpace

end AlgebraicGeometry.AlgebraicSpace
