
set_option autoImplicit false

universe u
universe v
variable {α : Type u}
variable [DecidableEq α]
variable {β : Type v}


def fun_upd : (d : β) → (α → Option β) → α → (β → β) → (α → Option β) :=
  fun d f x k x' => if x' = x then some (k ((f x').getD d)) else f x'

theorem fun_upd_eq (d : β) (f : α → Option β) (x : α) (k : β → β) :
  (fun_upd d f x k x) = some (k ((f x).getD d)) := by
  simp [fun_upd]

theorem fun_upd_ne (d : β) (f : α → Option β) (x₁ x₂ : α) (k : β → β) (h : x₂ ≠ x₁):
  (fun_upd d f x₁ k x₂) = f x₂ := by
  simp [fun_upd, h]

namespace Trie.Abstract

/--
A very abstract idea of a trie data structure. We prove the relevant theorems about
their properties here, and show that more refined implementations behave like these.
-/
inductive Trie (α : Type u) (β : Type v) where
  | node (val : Option β) (c : α → Option (Trie α β)) : Trie α β

namespace Trie


@[simp]
def val : Trie α β → Option β
  | .node v _ => v

@[simp]
def c : Trie α β → α → Option (Trie α β)
  | .node _ c => c

def empty : Trie α β := .node none (fun _ => .none)

def insert (t : Trie α β) : List α → β → Trie α β
  | [], v => .node (some v) t.c
  | k::ks, v => .node t.val <|
      fun_upd empty t.c k fun t => t.insert ks v

def find? (t : Trie α β) : List α → Option β
  | [] => t.val
  | k::ks => match t.c k with
    | none => none
    | some t => t.find? ks

@[simp]
theorem find?_empty (k : List α) : (empty : Trie α β).find? k = none :=  by
  cases k <;> simp [empty, find?]

theorem find?_insert_eq (t : Trie α β) (k : List α) (v : β) :
    (t.insert k v).find? k = some v := by
  induction k generalizing t with
  | nil => simp [insert, find?, val]
  | cons k ks ih =>
    cases t with | _ v' c =>
    simpa [insert, find?, fun_upd] using ih _

theorem find?_insert_neq (t : Trie α β) (k k' : List α) (hne : k ≠ k') (v : β) :
    (t.insert k v).find? k' = t.find? k' := by
  induction k generalizing t k' with
  | nil =>
    cases k' with | nil => contradiction | cons k' ks' =>
    cases t with | _ v' c =>
    simp [find?, insert]
  | cons k ks ih =>
    cases t with | _ v' c =>
    cases k' with
    | nil => simp [find?, insert]
    | cons k' ks' =>
      if hk : k' = k then
        subst k'
        have : ks ≠ ks' := by intro h; apply hne; cases h; rfl
        simp [insert, find?, hne, fun_upd, Option.getD, ih, this]
        cases c k <;> simp
      else
        simp [insert, find?, fun_upd, hk]


end Trie

end Trie.Abstract

theorem Array.drop_data_cons {α : Type _} (as : Array α) (i : Nat) (h : i < as.size) :
  as.data.drop i = as[i] :: as.data.drop (i + 1) := by sorry

theorem Array.drop_data_nil {α : Type _} (as : Array α) (i : Nat) (h : ¬ i < as.size) :
  as.data.drop i = [] := by sorry

@[simp]
theorem Array.extract_data {α} (as : Array α) (i : Nat) (j : Nat) :
  (as.extract i j).data = (as.data.take j).drop i := by sorry

theorem Array.modify_data {α} (as : Array α) (i : Nat) (f : α → α) (h : i < as.size):
    (Array.modify as i f).data = as.data.take i ++ [f as[i]] ++ as.data.drop (i + 1) := by sorry

theorem Array.data_getElem {α} (as : Array α) (i : Nat) (h : i < as.size) :
  as.data[i] = as[i] := rfl

theorem Array.size_extract {α} (as : Array α) (start stop : Nat) :
    Array.size (Array.extract as start stop) = min stop (Array.size as) - start :=
  by sorry

theorem Array.get_extract {α} {i : Nat} {as : Array α} {start stop : Nat} (h : i < Array.size (Array.extract as start stop)) :
 (Array.extract as start stop)[i] = as[start + i]'(by simp [Array.size_extract] at *; omega) := sorry

theorem Array.attach {α} (as : Array α) : Array {x : α // x ∈ as} := by sorry


@[simp]
theorem Array.attach_singleton {α} (a : α) : #[a].attach = #[⟨a, .mk (by simp)⟩] := sorry

@[simp]
theorem Array.map_attach {α β} (xs : Array α) (f : α → β) :
  xs.attach.map (fun ⟨x, _⟩ => f x) = xs.map f := sorry

@[simp]
theorem Array.map_two {α β} (x₁ x₂ : α) (f : α → β) :
  #[x₁, x₂].map f = #[f x₁, f x₂] := sorry

-- TODO: Lemma has wrong name in std
axiom Array.getElem_mem :
  ∀ {α : Type u} {i : Nat} (a : Array α) (h : i < Array.size a), a[i] ∈ a

namespace Trie.AbstractArray

/--
Like `Trie.Abstract.Trie`, but the operations (not the implementation!) uses arrays for keys.
-/
abbrev Trie := @Trie.Abstract.Trie

namespace Trie

def empty := @Trie.Abstract.Trie.empty

def insert (t : Trie α β) (ks : Array α) (v : β) : Trie α β := go t 0
  where
  go t i := if h : i < ks.size then
    let k := ks[i]
    .node t.val (fun_upd empty t.c k fun t => go t (i + 1))
  else
    .node (some v) t.c
  termination_by ks.size - i

derive_induction insert.go

def find? (t : Trie α β) (ks : Array α) : Option β := go t 0
  where
  go t i := if h : i < ks.size then
    match t.c ks[i] with
    | none => none
    | some t => go t (i + 1)
  else
    t.val
  termination_by ks.size - i

derive_induction find?.go

/-
We first specify the operations on Arrays via their abstract counter-parts on lists.
-/

theorem insert_go_data (t : Trie α β) (ks : Array α) (v : β) (i : Nat) :
    insert.go ks v t i = Abstract.Trie.insert t (ks.data.drop i) v := by
  induction t, i using insert.go.induct (ks := ks) (v := v)
  case case1 t i hi IH =>
    unfold insert.go; simp only [hi, ↓reduceDite]
    simp [Abstract.Trie.insert, Array.drop_data_cons, empty, hi, IH]
  case case2 t i hi =>
    unfold insert.go; simp only [hi, ↓reduceDite]
    simp only [Abstract.Trie.insert, Array.drop_data_nil (h := hi)]

theorem insert_spec (t : Trie α β) (ks : Array α) (v : β) :
    insert t ks v = Abstract.Trie.insert t ks.data v := by simp [insert, insert_go_data]

theorem find?_go_data (t : Trie α β) (ks : Array α)  (i : Nat) :
    find?.go ks t i = Abstract.Trie.find? t (ks.data.drop i) := by
  induction t, i using find?.go.induct (ks := ks)
  case case1 t i hi IH =>
    unfold find?.go; simp only [hi, ↓reduceDite]
    simp only [Abstract.Trie.find?, Array.drop_data_cons, hi, IH]
  case case2 t i hi =>
    unfold find?.go; simp only [hi, ↓reduceDite]
    simp only [Abstract.Trie.find?, Array.drop_data_nil (h := hi)]

theorem find?_spec (t : Trie α β) (ks : Array α) :
    find? t ks = Abstract.Trie.find? t ks.data := by simp [find?, find?_go_data]

/-
Then the actual user-facing theorems follow quickly.
-/

theorem find?_empty (k : Array α) : find? (empty : Trie α β) k = none := by
  simp [find?_spec, Abstract.Trie.find?_empty, empty]

theorem find?_insert_eq (t : Trie α β) (k : Array α) (v : β) :
    (t.insert k v).find? k = some v := by
  simpa [insert_spec, find?_spec] using Abstract.Trie.find?_insert_eq _ _ _

theorem find?_insert_neq (t : Trie α β) (k k' : Array α) (hne : k ≠ k') (v : β) :
    (t.insert k v).find? k' = t.find? k' := by
  have hne' : k.data ≠ k'.data := by intro h; apply hne; cases k; cases k'; simpa
  simpa [insert_spec, find?_spec] using Abstract.Trie.find?_insert_neq _ _ _ hne' _

end Trie

end Trie.AbstractArray


-- Helper functions for associative lists and arrays

namespace AssocList

def upsert (ks : List α) (vs : List β) (k : α) (f : Option β → β) : List α × List β :=
  match ks, vs with
  | k'::ks, v::vs =>
    if k = k' then
      (k'::ks, f (some v) :: vs)
    else
      let (ks, vs) := upsert ks vs k f
      (k'::ks, v::vs)
  | _, _ => ([k], [f none])

def find? (ks : List α) (vs : List β) (k : α) : Option β :=
  match ks, vs with
  | k'::ks, v::vs =>
    if k = k' then
      some v
    else
      find? ks vs k
  | _, _ => none

@[simp]
theorem find?_nil (vs : List β) (k : α) : find? [] vs k = none := by
  simp [find?]

theorem find?_upsert_eq (ks : List α) (vs : List β) (k : α) (f : Option β → β) :
    find? (upsert ks vs k f).1 (upsert ks vs k f).2 k = some (f (find? ks vs k)) := by
  induction ks generalizing vs with
  | nil => simp [upsert, find?]
  | cons k' ks ih =>
    cases vs with
    | nil => simp [upsert, find?]
    | cons v vs =>
      simp [upsert]
      split <;> simp [find?]
      next heq => subst k'; simp
      next hne => simp [hne]; apply ih

theorem find?_upsert_ne (ks : List α) (vs : List β) (k₁ k₂ : α) (f : Option β → β) (h : k₂ ≠ k₁) :
    find? (upsert ks vs k₁ f).1 (upsert ks vs k₁ f).2 k₂ = find? ks vs k₂ := by
  induction ks generalizing vs with
  | nil => simp [upsert, find?, h]
  | cons k' ks ih =>
    cases vs with
    | nil => simp [upsert, find?, h]
    | cons v vs =>
      simp [upsert]
      split <;> simp [find?]
      next heq => subst k'; simp [h]
      next hne => split <;> simp [*]

end AssocList

namespace AssocArray

def upsert (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) : Array α × Array β :=
  go 0
  where
  go i :=
    if hi : i < ks.size then
      if hj : i < vs.size then
        if k = ks[i] then
          (ks, vs.modify i (fun v => f (some v)))
        else
          go (i + 1)
      else
        ((ks.extract 0 i).push k, vs.push (f none))
    else
      (ks.push k, (vs.extract 0 i).push (f none))
  termination_by ks.size - i

derive_induction upsert.go

@[simp]
theorem upsert_nil (k : α) (f : Option β → β) : upsert #[] #[] k f = (#[k], #[f none]) := rfl

theorem upsert_singleton_ne (k₁ k₂ : α) (v₁ : β) (f : Option β → β) (hne : k₂ ≠ k₁):
  upsert #[k₁] #[v₁] k₂ f = (#[k₁, k₂], #[v₁, f none]) := by
  unfold upsert upsert.go
  simp [hne, Array.getElem_eq_data_get, List.get]
  rfl

def biDataDrop {α} {β} (pair : Array α × Array β) (i : Nat) : List α × List β :=
  (pair.1.data.drop i, pair.2.data.drop i)

theorem Array.data_ext {α} (a₁ a₂ : Array α) : (a₁ = a₂ ↔ a₁.data = a₂.data) := by
  constructor
  · intro h; subst h; rfl
  · intro h; cases a₁; cases a₂; simpa using h


def upsert_go_spec (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) (i : Nat) :
    upsert.go ks vs k f i =
      let (ks', vs') := AssocList.upsert (ks.data.drop i) (vs.data.drop i) k f;
      ((ks.data.take i ++ ks').toArray, (vs.data.take i ++ vs').toArray) := by
  induction i using upsert.go.induct (ks := ks) (vs := vs) (k := k) (f := f)
  case case1 i hi hj heq =>
    unfold upsert.go; simp only [hi, hj, heq, ↓reduceIte, ↓reduceDite]
    simp [Array.data_ext, AssocList.upsert, Array.drop_data_cons, hi, hj, ↓reduceIte,
      ↓reduceDite, Array.modify_data, hj]
    simp [← Array.data_getElem, List.get_drop_eq_drop ]
  case case2 i hi hj hneq IH =>
    unfold upsert.go; simp only [hi, hj, hneq, ↓reduceIte, ↓reduceDite]
    simp only [Array.data_ext, AssocList.upsert, Array.drop_data_cons, hi, hj, hneq,
      ↓reduceIte, ↓reduceDite]
    rw [IH]
    simp [Array.data_ext, ← List.take_concat_get, hi, hj, Array.data_getElem]
  case case3 i hi hj =>
    have : vs.data.length ≤ i := by unfold Array.size at hj; omega
    unfold upsert.go; simp only [hi, hj, ↓reduceIte, ↓reduceDite]
    simp [Array.data_ext, AssocList.upsert, Array.drop_data_cons, hi, hj, ↓reduceIte, ↓reduceDite,
      List.take_length_le, List.drop_length_le, this]
  case case4 i hi =>
    have : ks.data.length ≤ i := by unfold Array.size at hi; omega
    unfold upsert.go; simp only [hi, ↓reduceIte, ↓reduceDite]
    simp [Array.data_ext, AssocList.upsert, Array.drop_data_cons, hi, ↓reduceIte, ↓reduceDite,
      List.take_length_le, List.drop_length_le, this]


def upsert_spec (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) :
    upsert ks vs k f =
      let (ks', vs') := AssocList.upsert ks.data vs.data k f;
      (ks'.toArray, vs'.toArray) := by simp [upsert, upsert_go_spec]

def find?' (ks : Array α) (vs : Array β) (k : α) : Option {x : β // x ∈ vs} := go 0
  where
  go i :=
    if hi : i < ks.size then
      if hj : i < vs.size then
        if k = ks[i] then
          some ⟨vs[i], Array.getElem_mem _ hj⟩
        else
          go (i + 1)
      else
        none
    else
      none
  termination_by ks.size - i

derive_induction find?'.go

def find? (ks : Array α) (vs : Array β) (k : α) : Option β := (find?' ks vs k).map (·.val)

def find?'_go_spec (ks : Array α) (vs : Array β) (k : α) (i : Nat) :
    (find?'.go ks vs k i).map (·.val) = AssocList.find? (ks.data.drop i) (vs.data.drop i) k := by
  induction i using find?'.go.induct (ks := ks) (vs := vs) (k := k)
  case case1 i hi hj heq =>
    unfold find?'.go; simp only [hi, hj, heq, ↓reduceIte, ↓reduceDite]
    simp [Array.data_ext, AssocList.find?, Array.drop_data_cons, hi, hj, heq, ↓reduceIte, ↓reduceDite]
  case case2 i hi hj hneq IH =>
    unfold find?'.go; simp only [hi, hj, hneq, ↓reduceIte, ↓reduceDite]
    simp only [Array.data_ext, AssocList.find?, Array.drop_data_cons, hi, hj, hneq,
      ↓reduceIte, ↓reduceDite, IH]
  case case3 i hi hj =>
    have : vs.data.length ≤ i := by unfold Array.size at hj; omega
    unfold find?'.go; simp only [hi, hj, ↓reduceIte, ↓reduceDite]
    simp only [Array.data_ext, AssocList.find?, Array.drop_data_cons, hi, hj, ↓reduceIte, ↓reduceDite,
      List.drop_length_le, this, Option.map_none']
  case case4 i hi =>
    have : ks.data.length ≤ i := by unfold Array.size at hi; omega
    unfold find?'.go; simp only [hi, ↓reduceIte, ↓reduceDite]
    simp only [Array.data_ext, AssocList.find?, Array.drop_data_cons, hi, ↓reduceIte, ↓reduceDite,
      List.drop_length_le, this, Option.map_none']

def find?'_spec (ks : Array α) (vs : Array β) (k : α) :
    (find?' ks vs k).map (·.val) = AssocList.find? ks.data vs.data k :=
  by simp [find?', find?'_go_spec]

def find?_spec (ks : Array α) (vs : Array β) (k : α) :
    find? ks vs k = AssocList.find? ks.data vs.data k := find?'_spec _ _ _

@[simp]
theorem find?_nil (vs : Array β) (k : α) : find? #[] vs k = none := by
  simp [find?_spec]

theorem find?_upsert_eq (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) :
    find? (upsert ks vs k f).1 (upsert ks vs k f).2 k = some (f (find? ks vs k)) := by
  simp [upsert_spec, find?_spec]
  apply AssocList.find?_upsert_eq

theorem find?_upsert_ne (ks : Array α) (vs : Array β) (k₁ k₂ : α) (f : Option β → β)  (h : k₂ ≠ k₁) :
    find? (upsert ks vs k₁ f).1 (upsert ks vs k₁ f).2 k₂ = find? ks vs k₂:= by
  simp [upsert_spec, find?_spec]
  apply AssocList.find?_upsert_ne (h := h)


end AssocArray

namespace Trie.Array

/--
A more realistic implementation, using Arrays instead of functions.
-/
inductive Trie (α : Type u) (β : Type v) where
  | node (val : Option β) (ks : Array α) (vs : Array (Trie α β)) : Trie α β

namespace Trie

def empty : Trie α β := .node none #[] #[]

def insert (t : Trie α β) (ks : Array α) (v : β) : Trie α β := go t 0 where
  go | .node val ks' vs, i =>
      if h : i < ks.size then
        let (ks'', vs'') := AssocArray.upsert ks' vs ks[i] fun t? =>
          go (t?.getD empty) (i + 1)
        .node val ks'' vs''
      else
        .node (some v) ks' vs
  termination_by _ i => ks.size - i

def find? (t : Trie α β) (ks : Array α) : Option β := go t 0 where
  go | .node val ks' vs, i =>
      if h : i < ks.size then
        match AssocArray.find? ks' vs ks[i] with
        | none => none
        | some t => go t (i + 1)
      else
        val
  termination_by _ i => ks.size - i

derive_induction find?.go

def toAbstractArray : Trie α β → AbstractArray.Trie α β
  | .node val ks vs => .node val fun k =>
    match AssocArray.find?' ks vs k with
    | none => none
    | some ⟨t, _⟩ => some t.toAbstractArray
termination_by t => sizeOf t

def toAbstractArray_eq (val : Option β) (ks : Array α) (vs : Array (Trie α β)) :
  toAbstractArray (Trie.node val ks vs) = .node val fun k =>
    match AssocArray.find? ks vs k with
    | none => none
    | some t => some t.toAbstractArray := by
  conv => left; unfold toAbstractArray
  congr 1
  funext k
  unfold AssocArray.find?
  simp [Option.map]
  split <;> simp [*]


@[simp]
theorem empty_spec :
    (empty : Trie α β).toAbstractArray = AbstractArray.Trie.empty := by
  simp [toAbstractArray, empty, AbstractArray.Trie.empty]
  rfl

theorem find?_go_spec (t : Trie α β) (ks : Array α) (i : Nat) :
    find?.go ks t i = AbstractArray.Trie.find?.go ks t.toAbstractArray i := by
  induction t, i using find?.go.induct (ks := ks)
  case case1 v ks' vs i hi IH =>
    unfold find?.go
    unfold AbstractArray.Trie.find?.go
    simp only [hi, ↓reduceDite]
    simp only [toAbstractArray_eq, Option.getD, Abstract.Trie.c, IH]
    split <;> simp
  case case2 v ks' vs i hi =>
    unfold find?.go
    unfold AbstractArray.Trie.find?.go
    simp only [hi, ↓reduceDite]
    simp only [toAbstractArray_eq, Abstract.Trie.val]
    done

theorem find?_spec (t : Trie α β) (ks : Array α):
    t.find? ks = t.toAbstractArray.find? ks := by
  simp [find?, AbstractArray.Trie.find?, find?_go_spec]

theorem insert_go_spec (t : Trie α β) (ks : Array α) (i : Nat) (v : β):
    (insert.go ks v t i).toAbstractArray  = AbstractArray.Trie.insert.go ks v t.toAbstractArray i := by
  induction t, i using find?.go.induct (ks := ks)
  case case1 v ks' vs i hi IH =>
    unfold insert.go AbstractArray.Trie.insert.go
    simp only [hi, ↓reduceDite]
    simp only [toAbstractArray_eq, Abstract.Trie.c]
    congr 1
    funext k
    if h : k = ks[i] then
      simp only [↓reduceIte, h, AssocArray.find?_upsert_eq, IH, fun_upd_eq]
      simp [Option.getD]
      split <;> simp [*]
    else
      simp only [↓reduceIte, h, AssocArray.find?_upsert_ne (h := h), fun_upd_ne (h := h)]
  case case2 v ks' vs i hi =>
    unfold insert.go
    unfold AbstractArray.Trie.insert.go
    simp only [hi, ↓reduceDite]
    simp only [toAbstractArray, Abstract.Trie.c]

theorem insert_spec (t : Trie α β) (ks : Array α) (v : β):
    (insert t ks v).toAbstractArray  = AbstractArray.Trie.insert t.toAbstractArray ks v :=
  insert_go_spec ..


theorem find?_empty (k : Array α) : find? (empty : Trie α β) k = none := by
  simp [find?_spec, AbstractArray.Trie.find?_empty]

theorem find?_insert_eq (t : Trie α β) (k : Array α) (v : β) :
    (t.insert k v).find? k = some v := by
  simp [insert_spec, find?_spec]
  apply AbstractArray.Trie.find?_insert_eq

theorem find?_insert_neq (t : Trie α β) (k k' : Array α) (hne : k ≠ k') (v : β) :
    (t.insert k v).find? k' = t.find? k' := by
  simpa [insert_spec, find?_spec] using AbstractArray.Trie.find?_insert_neq _ _ _ hne _

end Trie

end Trie.Array

namespace Trie.Compressed

/--
Now additing path compression.
-/
inductive Trie (α : Type u) (β : Type v) where
  | leaf (val : Option β)
  | path (val : Option β) (ps : Array α) (hps : 0 < ps.size) (t : Trie α β) : Trie α β
  | node (val : Option β) (ks : Array α) (vs : Array (Trie α β)) : Trie α β

namespace Trie

def empty : Trie α β := .leaf none

def commonPrefix (xs : Array α) (ys : Array α) (offset1 : Nat) : Nat :=
  let rec loop (i : Nat) : Nat :=
    if h : offset1 + i < xs.size then
      if h' : i < ys.size then
        if xs[offset1 + i] = ys[i] then
          loop (i + 1)
        else
          i
      else
        i
    else
      i
    termination_by ys.size - i
  loop 0

def hasPrefix (xs : Array α) (ys : Array α) (offset1 : Nat) : Bool :=
  let rec loop (i : Nat) : Bool :=
    if h' : i < ys.size then
      if h : offset1 + i < xs.size then
        if xs[offset1 + i] = ys[i] then
          loop (i + 1)
        else
          false
      else
        false
    else
      true
    termination_by ys.size - i
  loop 0
derive_induction hasPrefix.loop


theorem commonPrefix_loop_of_hasPrefix_loop (xs : Array α) (ys : Array α) (offset1 i : Nat)
    (hi : i ≤ ys.size) (h : hasPrefix.loop xs ys offset1 i = true) :
    commonPrefix.loop xs ys offset1 i = ys.size := by
  induction i using hasPrefix.loop.induct (xs := xs) (ys := ys) (offset1 := offset1)
  case case1 IH =>
    unfold hasPrefix.loop at h; simp [*] at h
    unfold commonPrefix.loop; simp [*]
    apply IH _ h
    omega
  case case2 | case3 => unfold hasPrefix.loop at h; simp [*] at h
  case case4 i hi =>
    unfold commonPrefix.loop; simp [*]
    omega

theorem commonPrefix_of_hasPrefix (xs : Array α) (ys : Array α) (offset1 : Nat)
    (h : hasPrefix xs ys offset1 = true) :
    commonPrefix xs ys offset1 = ys.size :=
  commonPrefix_loop_of_hasPrefix_loop xs ys offset1 0 (Nat.zero_le _) h

def mkPath (ps : Array α) (t : Trie α β) : Trie α β :=
  if h : 0 < ps.size  then .path none ps h t else t

def insert (t : Trie α β) (ks : Array α) (v : β) : Trie α β := go 0 t where
  go (i : Nat)
    | .leaf val =>
      if h : i < ks.size then
        path val (ks.extract i ks.size) (by simp [Array.size_extract]; omega) (.leaf (some v))
      else
        .leaf (some v)
    | .path val ps hps t' =>
      if h : i < ks.size then
        let j := commonPrefix ks ps i
        if hj : 0 < j then
          -- split common prefix, continue
          .path val (ps.extract 0 j) (by simp [Array.size_extract];omega) <| go (i + j) <|
              .mkPath (ps.extract j ps.size) t'
        else
          -- no common prefix, split off first key
          let c := ks[i]
          let c' := ps[0]'(by omega)
          let t := mkPath (ks.extract (i+1) ks.size) (.leaf (some v))
          let t'' := mkPath (ps.extract 1 ps.size) t'
          .node val #[c', c] #[t'', t] -- order matters for refinemnet proof!
      else
        .path (some v) ps hps t'
    | .node val ks' vs =>
      if h : i < ks.size then
        let (ks'', vs'') := AssocArray.upsert ks' vs ks[i] fun t? =>
          go (i + 1) (t?.getD empty)
        .node val ks'' vs''
      else
        .node (some v) ks' vs
  termination_by ks.size - i
  decreasing_by all_goals simp_wf; omega

def find? (t : Trie α β) (ks : Array α) : Option β := go 0 t where
  go
    | i, .leaf val =>
      if i < ks.size then
        none
      else
        val
    | i, path val ps _ t' =>
      if i < ks.size then
        if hasPrefix ks ps i then
          go (i + ps.size) t'
        else
          none
      else
        val
    | i, .node val ks' vs =>
      if h : i < ks.size then
        match AssocArray.find? ks' vs ks[i] with
        | none => none
        | some t => go (i + 1) t
      else
        val
  termination_by i => ks.size - i
  decreasing_by all_goals simp_wf; omega

derive_induction find?.go

def uncompressPath (val : Option β) (ps : Array α) (i : Nat) (t : Array.Trie α β) : Array.Trie α β :=
  if h : i < ps.size then
    .node val #[ps[i]] #[uncompressPath none ps (i + 1) t]
  else
    t
termination_by ps.size - i
derive_induction uncompressPath


noncomputable
def uncompress : Trie α β → Array.Trie α β
  | .leaf val => .node val #[] #[]
  | .node val ks vs => .node val ks (vs.attach.map fun ⟨t, _⟩ => t.uncompress)
  | .path val ps _ t => uncompressPath val ps 0 (t.uncompress)
termination_by t => sizeOf t

@[simp]
theorem empty_spec : (empty : Trie α β).uncompress = .empty := by rfl

@[simp]
theorem uncompressPath_extract (val : Option β) (ks : Array α) (i j : Nat) t :
  uncompressPath val (Array.extract ks i (Array.size ks)) j t =
  uncompressPath val ks (i + j) t := by
  unfold uncompressPath;
  simp [Array.size_extract, Array.get_extract]
  split
  next hj =>
    have : i + j < Array.size ks := by omega
    simp [this, uncompressPath_extract (ks := ks) (j := j+1)]
    rfl
  next hj =>
    have : ¬ (i + j < Array.size ks) := by omega
    simp [this]
termination_by ks.size - j
decreasing_by simp_wf; omega

@[simp]
theorem uncompress_mkPath (ps : Array α) (t : Trie α β):
    uncompress (mkPath ps t) = uncompressPath none ps 0 t.uncompress := by
  unfold mkPath
  split
  next hps => simp [uncompress]
  next hps => unfold uncompressPath; simp [hps]


theorem insert_go_spec (t : Trie α β) (ks : Array α) (i : Nat) (v : β):
    (insert.go ks v i t).uncompress  = .insert.go ks v t.uncompress i := by
  cases t with
  | leaf val =>
    simp [insert.go, *, uncompress]
    split
    next hi =>
      simp [uncompress]
      sorry -- insert into leaf is uncompressPath
    next hi0 =>
      simp [insert.go, *, uncompress, Array.Trie.insert.go]
  | path val ps hps t' =>
    simp [insert.go, *, uncompress]
    split
    next hi =>
      split
      next hcommonPrefix_pos =>
        simp [uncompress]
        rw [insert_go_spec]
        simp
        sorry -- insert into uncompressPath goes past common prefix
      next hcommonPrefix_0 =>
        have : commonPrefix ks ps i = 0 := by omega
        have hne : ks[i] ≠ ps[0] := by sorry
        simp [uncompress, this, Array.Trie.insert.go, hi]
        conv => right; unfold uncompressPath
        simp [hps, Array.Trie.insert.go, hi, AssocArray.upsert_singleton_ne (hne := hne)]
        sorry -- insert into empty is uncompressPath
    next hi0 =>
      simp [insert.go, *, uncompress, Array.Trie.insert.go]
      unfold uncompressPath
      simp [hps, Array.Trie.insert.go, hi0]
  | node val ks' cs =>
    simp [insert.go]
    split
    next hi =>
      simp [uncompress, Array.Trie.insert.go, hi]
      constructor
      -- Array.map commutes with AssocArray.upsert
      · sorry
      · sorry
    next hi0 =>
      simp [insert.go, *, uncompress, Array.Trie.insert.go]
termination_by ks.size - i
decreasing_by simp_wf; omega
