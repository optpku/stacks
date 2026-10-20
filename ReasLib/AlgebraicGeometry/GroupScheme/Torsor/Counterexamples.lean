module

public import ReasLib.AlgebraicGeometry.GroupScheme.RepresentableTorsor
public import ReasLib.CategoryTheory.Sites.Torsor.Basic

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupScheme

/-- For some group scheme, a surjective pseudo-torsor is not an fpqc torsor. -/
theorem existsSurjectivePseudoNotTorsor :
    ∃ (S : Scheme.{u}) (G : Grp (Over S)) (X : Mod (Over S) G.X),
      Mod.IsPseudoTorsor X ∧ Surjective X.X.hom ∧ ¬ IsTorsor G X := sorry

/-- For some group scheme, an fppf sheaf torsor has nonrepresentable carrier. -/
theorem existsNonrepresentableFppfTorsor :
    ∃ (S : Scheme.{u}) (G : Grp (Over S))
      (P : Sheaf.Torsor (representableGroup .fppf G)),
      ¬ P.carrier.1.IsRepresentable := sorry

/-- For some group scheme, an fpqc torsor is not an fppf torsor. -/
theorem existsTorsorNotFppf :
    ∃ (S : Scheme.{u}) (G : Grp (Over S)) (X : Mod (Over S) G.X),
      IsTorsor G X ∧ ¬ IsStandardTorsor G X .fppf := sorry

end AlgebraicGeometry.GroupScheme
