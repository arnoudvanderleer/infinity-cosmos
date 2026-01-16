import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

open CategoryTheory Simplicial

namespace SSet

namespace Edge

structure IsIso {X : SSet} {x₀ x₁ : X _⦋0⦌} (hom : Edge x₀ x₁) where
  inv            : Edge x₁ x₀
  hom_inv_id     : Edge.CompStruct hom inv (Edge.id x₀)
  inv_hom_id     : Edge.CompStruct inv hom (Edge.id x₁)

namespace IsIso

lemma id_comp_id_aux
  {X : SSet}
  {l m n : ℕ}
  {f : ⦋n⦌ ⟶ ⦋m⦌}
  {g : ⦋m⦌ ⟶ ⦋l⦌}
  {h : ⦋n⦌ ⟶ ⦋l⦌}
  (x : X _⦋l⦌)
  (e : f ≫ g = h)
  : X.map f.op (X.map g.op x) = X.map h.op x
  := by
    show ((X.map _ ≫ X.map _) x = X.map _ x)
    rw [← X.map_comp]
    rw [← op_comp]
    congrm X.map (Quiver.Hom.op ?_) x
    exact e

def id_comp_id {X : SSet} (x : X _⦋0⦌) : Edge.CompStruct (Edge.id x) (Edge.id x) (Edge.id x) := .mk
  (X.map (Opposite.op (SimplexCategory.Hom.mk ⟨fun a ↦ 0, monotone_const⟩)) x)
  (by apply id_comp_id_aux; decide)
  (by apply id_comp_id_aux; decide)
  (by apply id_comp_id_aux; decide)

def IsIso_id {X : SSet} (x : X _⦋0⦌) : IsIso (Edge.id x) where
  inv := Edge.id x
  hom_inv_id := id_comp_id x
  inv_hom_id := id_comp_id x

def IsIso_inv {X : SSet} {x₀ x₁ : X _⦋0⦌} {hom : Edge x₀ x₁} (I : IsIso hom) : IsIso I.inv where
  inv := hom
  hom_inv_id := I.inv_hom_id
  inv_hom_id := I.hom_inv_id

end IsIso

end Edge

end SSet
