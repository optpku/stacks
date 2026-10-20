module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Locality
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.17.2: for a locally Noetherian scheme, universal catenarity is equivalent to
universal catenarity on an open cover, of every affine-open section ring, and of the section
rings on an affine open cover. -/
@[stacks 02J9] #check
  (AlgebraicGeometry.universallyCatenary_tfae :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian S],
      List.TFAE
        [ AlgebraicGeometry.UniversallyCatenary S,
          ∃ 𝒰 : S.OpenCover,
            ∀ i : 𝒰.I₀, AlgebraicGeometry.UniversallyCatenary (𝒰.X i),
          ∀ U : S.affineOpens, UniversallyCatenaryRing.{u, u} (Γ(S, U)),
          ∃ 𝒰 : S.AffineOpenCover,
            ∀ i : 𝒰.I₀,
              UniversallyCatenaryRing.{u, u} (Γ(S, (𝒰.f i).opensRange)) ])

/- Lemma 29.17.2 (moreover): every scheme locally of finite type over a universally catenary
scheme is universally catenary. -/
@[stacks 02J9] #check
  (AlgebraicGeometry.universallyCatenary_of_locallyOfFiniteType :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [AlgebraicGeometry.LocallyOfFiniteType f],
      AlgebraicGeometry.UniversallyCatenary X)
