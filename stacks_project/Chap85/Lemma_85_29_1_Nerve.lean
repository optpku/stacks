module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Nerve

/-!
# Groupoid-scheme nerve

The nerve construction is owned by the shared groupoid-scheme library.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.GroupoidScheme.simplicialScheme :
    {S : Scheme.{u}} → GroupoidScheme S → SimplicialObject Scheme.{u})
