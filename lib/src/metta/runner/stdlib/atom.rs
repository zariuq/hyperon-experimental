use hyperon_atom::*;
use hyperon_space::*;
use crate::metta::*;
use crate::metta::text::Tokenizer;
use crate::metta::types::{AtomType, get_atom_types, get_meta_type};
use hyperon_atom::matcher::atoms_are_equivalent;
use super::{grounded_op, regex};
use hyperon_atom::gnd::number::*;

use std::collections::HashMap;
use std::convert::TryInto;
use std::hash::{DefaultHasher, Hasher};

#[derive(Clone, Debug)]
pub struct UniqueAtomOp {}

grounded_op!(UniqueAtomOp, "unique-atom");

impl Grounded for UniqueAtomOp {
    fn type_(&self) -> Atom {
        Atom::expr([ARROW_SYMBOL, ATOM_TYPE_EXPRESSION, ATOM_TYPE_ATOM])
    }

    fn as_execute(&self) -> Option<&dyn CustomExecute> {
        Some(self)
    }
}

impl CustomExecute for UniqueAtomOp {    
    fn execute(&self, args: &[Atom]) -> Result<Vec<Atom>, ExecError> {    
        let arg_error = || ExecError::from("unique expects single expression atom as an argument");    
        let expr = TryInto::<&ExpressionAtom>::try_into(args.get(0).ok_or_else(arg_error)?)?;    
    
        let mut atoms: Vec<Atom> = expr.children().into();    
        let mut seen: Vec<Atom> = Vec::new();    
        atoms.retain(|x| {    
            let not_contained = !seen.iter().any(|seen_atom| atoms_are_equivalent(seen_atom, x));    
            if not_contained { seen.push(x.clone()) };    
            not_contained    
        });    
        Ok(vec![Atom::expr(atoms)])    
    }    
}


#[derive(Clone, Debug)]
pub struct UnionAtomOp {}

grounded_op!(UnionAtomOp, "union-atom");

impl Grounded for UnionAtomOp {
    fn type_(&self) -> Atom {
        Atom::expr([ARROW_SYMBOL, ATOM_TYPE_EXPRESSION, ATOM_TYPE_EXPRESSION, ATOM_TYPE_ATOM])
    }

    fn as_execute(&self) -> Option<&dyn CustomExecute> {
        Some(self)
    }
}

impl CustomExecute for UnionAtomOp {
    fn execute(&self, args: &[Atom]) -> Result<Vec<Atom>, ExecError> {
        let arg_error = || ExecError::from("union expects and executable LHS and RHS atom");
        let mut lhs: Vec<Atom> = TryInto::<&ExpressionAtom>::try_into(args.get(0).ok_or_else(arg_error)?)?.children().into();
        let rhs: Vec<Atom> = TryInto::<&ExpressionAtom>::try_into(args.get(1).ok_or_else(arg_error)?)?.children().into();

        lhs.extend(rhs);

        Ok(vec![Atom::expr(lhs)])
    }
}

#[derive(Clone, Debug)]
pub struct IntersectionAtomOp {}

grounded_op!(IntersectionAtomOp, "intersection-atom");

impl Grounded for IntersectionAtomOp {
    fn type_(&self) -> Atom {
        Atom::expr([ARROW_SYMBOL, ATOM_TYPE_EXPRESSION, ATOM_TYPE_EXPRESSION, ATOM_TYPE_ATOM])
    }

    fn as_execute(&self) -> Option<&dyn CustomExecute> {
        Some(self)
    }
}

/// Hashes an atom in a way which agrees with the equality of atoms: equal atoms
/// have equal hashes. Numbers are hashed by value because an integer is equal to
/// the float of the same value. Other grounded atoms do not contribute to the
/// hash, because their equality is not required to agree with their serialization.
fn atom_equality_hash(atom: &Atom) -> u64 {
    fn feed(atom: &Atom, hasher: &mut DefaultHasher) {
        match atom {
            Atom::Symbol(sym) => {
                hasher.write_u8(b'S');
                hasher.write(sym.name().as_bytes());
                hasher.write_u8(0);
            },
            Atom::Variable(var) => {
                hasher.write_u8(b'V');
                hasher.write(var.name().as_bytes());
                hasher.write_u8(0);
            },
            Atom::Expression(expr) => {
                hasher.write_u8(b'(');
                expr.children().iter().for_each(|child| feed(child, hasher));
                hasher.write_u8(b')');
            },
            Atom::Grounded(_) => match Number::from_atom(atom) {
                Some(number) => {
                    let value: f64 = number.into();
                    hasher.write_u8(b'N');
                    // 0.0 is equal to -0.0
                    hasher.write_u64(if value == 0.0 { 0 } else { value.to_bits() });
                },
                None => hasher.write_u8(b'G'),
            },
        }
    }

    let mut hasher = DefaultHasher::new();
    feed(atom, &mut hasher);
    hasher.finish()
}

/// A multiset of atoms which gives away each of its atoms at most once. Atoms
/// are compared by equality, the hash only narrows the search.
struct AtomMultiset<'a> {
    buckets: HashMap<u64, Vec<&'a Atom>>,
}

impl<'a> AtomMultiset<'a> {
    fn new(atoms: &'a [Atom]) -> Self {
        let mut buckets: HashMap<u64, Vec<&'a Atom>> = HashMap::new();
        for atom in atoms {
            buckets.entry(atom_equality_hash(atom)).or_default().push(atom);
        }
        Self{ buckets }
    }

    /// Removes one atom which is equal to `atom` from the multiset. Returns
    /// `false` when there is no such atom left.
    fn take(&mut self, atom: &Atom) -> bool {
        match self.buckets.get_mut(&atom_equality_hash(atom)) {
            Some(bucket) => match bucket.iter().rposition(|item| *item == atom) {
                Some(position) => { bucket.swap_remove(position); true },
                None => false,
            },
            None => false,
        }
    }
}


impl CustomExecute for IntersectionAtomOp {
    fn execute(&self, args: &[Atom]) -> Result<Vec<Atom>, ExecError> {
        let arg_error = || ExecError::from("intersection expects and executable LHS and RHS atom");
        let mut lhs: Vec<Atom> = TryInto::<&ExpressionAtom>::try_into(args.get(0).ok_or_else(arg_error)?)?.children().into();
        let rhs = TryInto::<&ExpressionAtom>::try_into(args.get(1).ok_or_else(arg_error)?)?.children();

        let mut rhs = AtomMultiset::new(rhs);
        lhs.retain(|candidate| rhs.take(candidate));

        Ok(vec![Atom::expr(lhs)])
    }
}

#[derive(Clone, Debug)]
pub struct MaxAtomOp {}

grounded_op!(MaxAtomOp, "max-atom");

impl Grounded for MaxAtomOp {
    fn type_(&self) -> Atom {
        Atom::expr([ARROW_SYMBOL, ATOM_TYPE_UNDEFINED, ATOM_TYPE_NUMBER])
    }

    fn as_execute(&self) -> Option<&dyn CustomExecute> {
        Some(self)
    }
}

impl CustomExecute for MaxAtomOp {
    fn execute(&self, args: &[Atom]) -> Result<Vec<Atom>, ExecError> {
        let arg_error = || ExecError::from("max-atom expects one argument: expression");
        let expr = TryInto::<&ExpressionAtom>::try_into(args.get(0).ok_or_else(arg_error)?)?;
        let children = expr.children();
        if children.is_empty() {
            Err(ExecError::from("Empty expression"))
        } else {
            children.into_iter().fold(Ok(f64::NEG_INFINITY), |res, x| {
                match (res, Number::from_atom(x)) {
                    (res @ Err(_), _) => res,
                    (_, None) => Err(ExecError::from(format!("Only numbers are allowed in expression: {}", expr))),
                    (Ok(max), Some(x)) => Ok(f64::max(max, x.into())),
                }
            })
        }.map(|max| vec![Atom::gnd(Number::Float(max))])
    }
}

#[derive(Clone, Debug)]
pub struct MinAtomOp {}

grounded_op!(MinAtomOp, "min-atom");

impl Grounded for MinAtomOp {
    fn type_(&self) -> Atom {
        Atom::expr([ARROW_SYMBOL, ATOM_TYPE_UNDEFINED, ATOM_TYPE_NUMBER])
    }

    fn as_execute(&self) -> Option<&dyn CustomExecute> {
        Some(self)
    }
}

impl CustomExecute for MinAtomOp {
    fn execute(&self, args: &[Atom]) -> Result<Vec<Atom>, ExecError> {
        let arg_error = || ExecError::from("min-atom expects one argument: expression");
        let expr = TryInto::<&ExpressionAtom>::try_into(args.get(0).ok_or_else(arg_error)?)?;
        let children = expr.children();
        if children.is_empty() {
            Err(ExecError::from("Empty expression"))
        } else {
            children.into_iter().fold(Ok(f64::INFINITY), |res, x| {
                match (res, Number::from_atom(x)) {
                    (res @ Err(_), _) => res,
                    (_, None) => Err(ExecError::from(format!("Only numbers are allowed in expression: {}", expr))),
                    (Ok(min), Some(x)) => Ok(f64::min(min, x.into())),
                }
            })
        }.map(|min| vec![Atom::gnd(Number::Float(min))])
    }
}

#[derive(Clone, Debug)]
pub struct SizeAtomOp {}

grounded_op!(SizeAtomOp, "size-atom");

impl Grounded for SizeAtomOp {
    fn type_(&self) -> Atom {
        Atom::expr([ARROW_SYMBOL, ATOM_TYPE_EXPRESSION, ATOM_TYPE_NUMBER])
    }

    fn as_execute(&self) -> Option<&dyn CustomExecute> {
        Some(self)
    }
}

impl CustomExecute for SizeAtomOp {
    fn execute(&self, args: &[Atom]) -> Result<Vec<Atom>, ExecError> {
        let arg_error = || ExecError::from("size-atom expects one argument: expression");
        let children = TryInto::<&ExpressionAtom>::try_into(args.get(0).ok_or_else(arg_error)?)?.children();
        let size = children.len();
        Ok(vec![Atom::gnd(Number::Integer(size as i64))])
    }
}

#[derive(Clone, Debug)]
pub struct IndexAtomOp {}

grounded_op!(IndexAtomOp, "index-atom");

impl Grounded for IndexAtomOp {
    fn type_(&self) -> Atom {
        Atom::expr([ARROW_SYMBOL, ATOM_TYPE_EXPRESSION, ATOM_TYPE_NUMBER, ATOM_TYPE_ATOM])
    }

    fn as_execute(&self) -> Option<&dyn CustomExecute> {
        Some(self)
    }
}

impl CustomExecute for IndexAtomOp {
    fn execute(&self, args: &[Atom]) -> Result<Vec<Atom>, ExecError> {
        let arg_error = || ExecError::from("index-atom expects two arguments: expression and atom");
        let children = TryInto::<&ExpressionAtom>::try_into(args.get(0).ok_or_else(arg_error)?)?.children();
        let index = args.get(1).and_then(Number::from_atom).ok_or_else(arg_error)?;
        match children.get(Into::<i64>::into(index) as usize) {
            Some(atom) => Ok(vec![atom.clone()]),
            None => Err(ExecError::from("Index is out of bounds")),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SubtractionAtomOp {}

grounded_op!(SubtractionAtomOp, "subtraction-atom");

impl Grounded for SubtractionAtomOp {
    fn type_(&self) -> Atom {
        Atom::expr([ARROW_SYMBOL, ATOM_TYPE_EXPRESSION, ATOM_TYPE_EXPRESSION, ATOM_TYPE_ATOM])
    }

    fn as_execute(&self) -> Option<&dyn CustomExecute> {
        Some(self)
    }
}

impl CustomExecute for SubtractionAtomOp {
    fn execute(&self, args: &[Atom]) -> Result<Vec<Atom>, ExecError> {
        let arg_error = || ExecError::from("subtraction expects and executable LHS and RHS atom");
        let mut lhs: Vec<Atom> = TryInto::<&ExpressionAtom>::try_into(args.get(0).ok_or_else(arg_error)?)?.children().into();
        let rhs = TryInto::<&ExpressionAtom>::try_into(args.get(1).ok_or_else(arg_error)?)?.children();

        let mut rhs = AtomMultiset::new(rhs);
        lhs.retain(|candidate| !rhs.take(candidate));

        Ok(vec![Atom::expr(lhs)])
    }
}

#[derive(Clone, Debug)]
pub struct GetTypeOp {
    space: DynSpace,
}

grounded_op!(GetTypeOp, "get-type");

impl GetTypeOp {
    pub fn new(space: DynSpace) -> Self {
        Self{ space }
    }
}

impl Grounded for GetTypeOp {
    fn type_(&self) -> Atom {
        Atom::expr([ARROW_SYMBOL, ATOM_TYPE_ATOM, ATOM_TYPE_UNDEFINED])
    }

    fn as_execute(&self) -> Option<&dyn CustomExecute> {
        Some(self)
    }
}

impl CustomExecute for GetTypeOp {
    fn execute(&self, args: &[Atom]) -> Result<Vec<Atom>, ExecError> {
        let arg_error = || ExecError::from("get-type expects single atom as an argument");
        let atom = args.get(0).ok_or_else(arg_error)?;
        let space = match args.get(1) {
            Some(space) => Atom::as_gnd::<DynSpace>(space)
                .ok_or("match expects a space as the first argument"),
            None => Ok(&self.space),
        }?;
        let types = get_atom_types(space, atom);
        if types.iter().any(AtomType::is_search_limit) {
            Ok(types.into_iter().filter(AtomType::is_search_limit).map(AtomType::into_error_unchecked).collect())
        } else if types.iter().all(AtomType::is_error) {
            Ok(vec![EMPTY_SYMBOL])
        } else {
            Ok(types.into_iter().filter(AtomType::is_valid).map(AtomType::into_atom).collect())
        }
    }
}

#[derive(Clone, Debug)]
pub struct GetMetaTypeOp { }

grounded_op!(GetMetaTypeOp, "get-metatype");

impl Grounded for GetMetaTypeOp {
    fn type_(&self) -> Atom {
        Atom::expr([ARROW_SYMBOL, ATOM_TYPE_ATOM, ATOM_TYPE_ATOM])
    }

    fn as_execute(&self) -> Option<&dyn CustomExecute> {
        Some(self)
    }
}

impl CustomExecute for GetMetaTypeOp {
    fn execute(&self, args: &[Atom]) -> Result<Vec<Atom>, ExecError> {
        let arg_error = || ExecError::from("get-metatype expects single atom as an argument");
        let atom = args.get(0).ok_or_else(arg_error)?;

        Ok(vec![get_meta_type(&atom)])
    }
}

#[derive(Clone, Debug)]
pub struct GetTypeSpaceOp {}

grounded_op!(GetTypeSpaceOp, "get-type-space");

impl Grounded for GetTypeSpaceOp {
    fn type_(&self) -> Atom {
        Atom::expr([ARROW_SYMBOL, ATOM_TYPE_SPACE, ATOM_TYPE_ATOM, ATOM_TYPE_ATOM])
    }

    fn as_execute(&self) -> Option<&dyn CustomExecute> {
        Some(self)
    }
}

impl CustomExecute for GetTypeSpaceOp {
    fn execute(&self, args: &[Atom]) -> Result<Vec<Atom>, ExecError> {
        let arg_error = || ExecError::from("get-type-space expects two arguments: space and atom");
        let space = args.get(0).ok_or_else(arg_error)?;
        let space = Atom::as_gnd::<DynSpace>(space).ok_or("get-type-space expects a space as the first argument")?;
        let atom = args.get(1).ok_or_else(arg_error)?;
        log::debug!("GetTypeSpaceOp::execute: space: {}, atom: {}", space, atom);
        let types = get_atom_types(space, atom);
        if types.iter().any(AtomType::is_search_limit) {
            Ok(types.into_iter().filter(AtomType::is_search_limit).map(AtomType::into_error_unchecked).collect())
        } else if types.iter().all(AtomType::is_error) {
            Ok(vec![EMPTY_SYMBOL])
        } else {
            Ok(types.into_iter().filter(AtomType::is_valid).map(AtomType::into_atom).collect())
        }
    }
}

pub(super) fn register_context_dependent_tokens(tref: &mut Tokenizer, space: &DynSpace) {
    let get_type_op = Atom::gnd(GetTypeOp::new(space.clone()));
    tref.register_token(regex(r"get-type"), move |_| { get_type_op.clone() });
}

pub(super) fn register_context_independent_tokens(tref: &mut Tokenizer) {
    let get_type_space_op = Atom::gnd(GetTypeSpaceOp{});
    tref.register_token(regex(r"get-type-space"), move |_| { get_type_space_op.clone() });
    let get_meta_type_op = Atom::gnd(GetMetaTypeOp{});
    tref.register_token(regex(r"get-metatype"), move |_| { get_meta_type_op.clone() });
    let min_atom_op = Atom::gnd(MinAtomOp{});
    tref.register_token(regex(r"min-atom"), move |_| { min_atom_op.clone() });
    let max_atom_op = Atom::gnd(MaxAtomOp{});
    tref.register_token(regex(r"max-atom"), move |_| { max_atom_op.clone() });
    let size_atom_op = Atom::gnd(SizeAtomOp{});
    tref.register_token(regex(r"size-atom"), move |_| { size_atom_op.clone() });
    let index_atom_op = Atom::gnd(IndexAtomOp{});
    tref.register_token(regex(r"index-atom"), move |_| { index_atom_op.clone() });
    let unique_op = Atom::gnd(UniqueAtomOp{});
    tref.register_token(regex(r"unique-atom"), move |_| { unique_op.clone() });
    let subtraction_op = Atom::gnd(SubtractionAtomOp{});
    tref.register_token(regex(r"subtraction-atom"), move |_| { subtraction_op.clone() });
    let intersection_op = Atom::gnd(IntersectionAtomOp{});
    tref.register_token(regex(r"intersection-atom"), move |_| { intersection_op.clone() });
    let union_op = Atom::gnd(UnionAtomOp{});
    tref.register_token(regex(r"union-atom"), move |_| { union_op.clone() });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metta::text::SExprParser;
    use crate::metta::runner::EnvBuilder;
    use hyperon_atom::gnd::str::Str;
    use hyperon_atom::gnd::bool::Bool;
    use crate::space::grounding::metta_space;
    use crate::metta::runner::run_program;
    use crate::metta::runner::Metta;
    use crate::metta::runner::stdlib::arithmetics::SumOp;
    use hyperon_common::{assert_eq_metta_results, assert_eq_no_order};

    #[test]
    fn metta_car_atom() {
        let result = run_program("!(car-atom (A $b))");
        assert_eq!(result, Ok(vec![vec![expr!("A")]]));
        let result = run_program("!(car-atom ($a B))");
        assert_eq!(result, Ok(vec![vec![expr!(a)]]));
        let result = run_program("!(car-atom ())");
        assert_eq!(result, Ok(vec![vec![expr!("Error" ("car-atom" ()) {Str::from_str("car-atom expects a non-empty expression as an argument")})]]));
        let result = run_program("!(car-atom A)");
        assert_eq!(result, Ok(vec![vec![expr!("Error" ("car-atom" "A") {Str::from_str("car-atom expects a non-empty expression as an argument")})]]));
    }

    #[test]
    fn metta_cdr_atom() {
        assert_eq!(run_program(&format!("!(cdr-atom (a b c))")), Ok(vec![vec![expr!("b" "c")]]));
        assert_eq!(run_program(&format!("!(cdr-atom ($a b $c))")), Ok(vec![vec![expr!("b" c)]]));
        assert_eq!(run_program(&format!("!(cdr-atom ())")), Ok(vec![vec![expr!("Error" ("cdr-atom" ()) {Str::from_str("cdr-atom expects a non-empty expression as an argument")})]]));
        assert_eq!(run_program(&format!("!(cdr-atom a)")), Ok(vec![vec![expr!("Error" ("cdr-atom" "a") {Str::from_str("cdr-atom expects a non-empty expression as an argument")})]]));
        assert_eq!(run_program(&format!("!(cdr-atom $a)")), Ok(vec![vec![expr!("Error" ("cdr-atom" a) {Str::from_str("cdr-atom expects a non-empty expression as an argument")})]]));
    }

    #[test]
    fn metta_size_atom() {
        assert_eq!(run_program(&format!("!(size-atom (5 4 3 2 1))")), Ok(vec![vec![expr!({Number::Integer(5)})]]));
        assert_eq!(run_program(&format!("!(size-atom ())")), Ok(vec![vec![expr!({Number::Integer(0)})]]));
    }

    #[test]
    fn metta_min_atom() {
        assert_eq!(run_program(&format!("!(min-atom (5 4 5.5))")), Ok(vec![vec![expr!({Number::Integer(4)})]]));
        assert_eq!(run_program(&format!("!(min-atom ())")), Ok(vec![vec![expr!("Error" ({ MinAtomOp{} } ()) "Empty expression")]]));
        assert_eq!(run_program(&format!("!(min-atom (3 A B 5))")), Ok(vec![vec![expr!("Error" ({ MinAtomOp{} } ({Number::Integer(3)} "A" "B" {Number::Integer(5)})) "Only numbers are allowed in expression: (3 A B 5)")]]));
        assert_eq!(run_program(&format!("(= (nums) (5 4 5.5)) !(min-atom (nums))")), Ok(vec![vec![expr!({Number::Integer(4)})]]));
    }

    #[test]
    fn metta_max_atom() {
        assert_eq!(run_program(&format!("!(max-atom (5 4 5.5))")), Ok(vec![vec![expr!({Number::Float(5.5)})]]));
        assert_eq!(run_program(&format!("!(max-atom ())")), Ok(vec![vec![expr!("Error" ({ MaxAtomOp{} } ()) "Empty expression")]]));
        assert_eq!(run_program(&format!("!(max-atom (3 A B 5))")), Ok(vec![vec![expr!("Error" ({ MaxAtomOp{} } ({Number::Integer(3)} "A" "B" {Number::Integer(5)})) "Only numbers are allowed in expression: (3 A B 5)")]]));
        assert_eq!(run_program(&format!("(= (nums) (5 4 5.5)) !(max-atom (nums))")), Ok(vec![vec![expr!({Number::Float(5.5)})]]));
    }

    #[test]
    fn metta_index_atom() {
        assert_eq!(run_program(&format!("!(index-atom (5 4 3 2 1) 2)")), Ok(vec![vec![expr!({Number::Integer(3)})]]));
        assert_eq!(run_program(&format!("!(index-atom (A B C D E) 5)")), Ok(vec![vec![expr!("Error" ({ IndexAtomOp{} } ("A" "B" "C" "D" "E") {Number::Integer(5)}) "Index is out of bounds")]]));
    }

    #[test]
    fn metta_filter_atom() {
        assert_eq!(run_program("!(filter-atom () $x (eval (if-error $x False True)))"), Ok(vec![vec![expr!()]]));
        assert_eq!(run_program("!(filter-atom (a (b) $c) $x (eval (if-error $x False True)))"), Ok(vec![vec![expr!("a" ("b") c)]]));
        assert_eq!(run_program("!(filter-atom (a (Error (b) \"Test error\") $c) $x (eval (if-error $x False True)))"), Ok(vec![vec![expr!("a" c)]]));
    }

    #[test]
    fn metta_map_atom() {
        assert_eq!(run_program("!(map-atom () $x ($x mapped))"), Ok(vec![vec![expr!()]]));
        assert_eq!(run_program("!(map-atom (a (b) $c) $x (mapped $x))"), Ok(vec![vec![expr!(("mapped" "a") ("mapped" ("b")) ("mapped" c))]]));
    }

    #[test]
    fn metta_foldl_atom() {
        assert_eq!(run_program("!(foldl-atom () 1 $a $b (eval (+ $a $b)))"), Ok(vec![vec![expr!({Number::Integer(1)})]]));
        assert_eq!(run_program("!(foldl-atom (1 2 3) 0 $a $b (eval (+ $a $b)))"), Ok(vec![vec![expr!({Number::Integer(6)})]]));
    }

    #[test]
    fn size_atom_op() {
        let res = SizeAtomOp{}.execute(&mut vec![expr!({Number::Integer(5)} {Number::Integer(4)} {Number::Integer(3)} {Number::Integer(2)} {Number::Integer(1)})]).expect("No result returned");
        assert_eq!(res, vec![expr!({Number::Integer(5)})]);
        let res = SizeAtomOp{}.execute(&mut vec![expr!()]).expect("No result returned");
        assert_eq!(res, vec![expr!({Number::Integer(0)})]);
    }

    #[test]
    fn min_atom_op() {
        let res = MinAtomOp{}.execute(&mut vec![expr!({Number::Integer(5)} {Number::Integer(4)} {Number::Float(5.5)})]).expect("No result returned");
        assert_eq!(res, vec![expr!({Number::Integer(4)})]);
        let res = MinAtomOp{}.execute(&mut vec![expr!({Number::Integer(5)} {Number::Integer(4)} "A")]);
        assert_eq!(res, Err(ExecError::from("Only numbers are allowed in expression: (5 4 A)")));
        let res = MinAtomOp{}.execute(&mut vec![expr!()]);
        assert_eq!(res, Err(ExecError::from("Empty expression")));
    }

    #[test]
    fn max_atom_op() {
        let res = MaxAtomOp{}.execute(&mut vec![expr!({Number::Integer(5)} {Number::Integer(4)} {Number::Float(5.5)})]).expect("No result returned");
        assert_eq!(res, vec![expr!({Number::Float(5.5)})]);
        let res = MaxAtomOp{}.execute(&mut vec![expr!({Number::Integer(5)} {Number::Integer(4)} "A")]);
        assert_eq!(res, Err(ExecError::from("Only numbers are allowed in expression: (5 4 A)")));
        let res = MaxAtomOp{}.execute(&mut vec![expr!()]);
        assert_eq!(res, Err(ExecError::from("Empty expression")));
        let res = MaxAtomOp{}.execute(&mut vec![expr!({Number::Integer(4)} {Str::from_str("5")})]);
        assert_eq!(res, Err(ExecError::from("Only numbers are allowed in expression: (4 \"5\")")));
    }

    #[test]
    fn index_atom_op() {
        let res = IndexAtomOp{}.execute(&mut vec![expr!({Number::Integer(5)} {Number::Integer(4)} {Number::Integer(3)} {Number::Integer(2)} {Number::Integer(1)}), expr!({Number::Integer(2)})]).expect("No result returned");
        assert_eq!(res, vec![expr!({Number::Integer(3)})]);
        let res = IndexAtomOp{}.execute(&mut vec![expr!({Number::Integer(5)} {Number::Integer(4)} {Number::Integer(3)} {Number::Integer(2)} {Number::Integer(1)}), expr!({Number::Integer(5)})]);
        assert_eq!(res, Err(ExecError::from("Index is out of bounds")));
    }

    #[test]
    fn test_error_is_used_as_an_argument() {
        let metta = Metta::new(Some(EnvBuilder::test_env()));
        let parser = SExprParser::new(r#"
            !(get-type Error)
            !(get-metatype Error)
            !(get-type (Error Foo Boo))
            !(Error (+ 1 2) (+ 1 +))
        "#);

        assert_eq_metta_results!(metta.run(parser), Ok(vec![
            vec![expr!("->" "Atom" "Atom" "ErrorType")],
            vec![expr!("Symbol")],
            vec![expr!("ErrorType")],
            vec![expr!("Error" ({SumOp{}} {Number::Integer(1)} {Number::Integer(2)}) ({SumOp{}} {Number::Integer(1)} {SumOp{}}))],
        ]));
    }


    #[test]
    fn unique_op() {
        let unique_op = UniqueAtomOp{};
        let actual = unique_op.execute(&mut vec![expr!(
                ("A" ("B" "C"))
                ("A" ("B" "C"))
                ("f" "g")
                ("f" "g")
                ("f" "g")
                "Z"
        )]).unwrap();
        assert_eq_no_order!(actual,
                   vec![expr!(("A" ("B" "C")) ("f" "g") "Z")]);
    }

     #[test]  
    fn unique_op_() {  
        let unique_op = UniqueAtomOp{};  
        let yonas = VariableAtom::new("yonas");  
        let tol = VariableAtom::new("tol");  
        let name_var = VariableAtom::new("name");  
    
        // Build the input: ((name $yonas) (name $tol) ($name $tol))  
        let input = Atom::expr([  
            Atom::expr([Atom::sym("name"), Atom::Variable(yonas.clone())]),  
            Atom::expr([Atom::sym("name"), Atom::Variable(tol.clone())]),  
            Atom::expr([Atom::Variable(name_var.clone()), Atom::Variable(tol.clone())])  
        ]);  
    
        let actual = unique_op.execute(&[input]).unwrap();  
        // the old implementation was giving us only ((name $yonas)) which is incorrect but now it is fixed
        // Expected: ((name $yonas) ($name $tol))  
        let expected = vec![Atom::expr([  
            Atom::expr([Atom::sym("name"), Atom::Variable(yonas.clone())]),  
            Atom::expr([Atom::Variable(name_var.clone()), Atom::Variable(tol.clone())])  
        ])];  
    
        assert_eq!(actual, expected);  
    }

    #[test]
    fn union_op() {
        let union_op = UnionAtomOp{};
        let actual = union_op.execute(&mut vec![expr!(
                ("A" ("B" "C"))
                ("A" ("B" "C"))
                ("f" "g")
                ("f" "g")
                ("f" "g")
                "Z"
            ), expr!(
                ("A" ("B" "C"))
                "p"
                "p"
                ("Q" "a")
            )]).unwrap();
        assert_eq_no_order!(actual,
                   vec![expr!(("A" ("B" "C")) ("A" ("B" "C"))
                        ("f" "g") ("f" "g") ("f" "g") "Z"
                        ("A" ("B" "C")) "p" "p" ("Q" "a"))]);
    }

    #[test]
    fn equal_atoms_have_equal_hashes() {
        let equal = [
            (Atom::sym("A"), Atom::sym("A")),
            (Atom::var("a"), Atom::var("a")),
            (expr!("A" ("B" x)), expr!("A" ("B" x))),
            (Atom::gnd(Number::Integer(1)), Atom::gnd(Number::Float(1.0))),
            (Atom::gnd(Number::Float(0.0)), Atom::gnd(Number::Float(-0.0))),
            (Atom::value(1), Atom::value(1)),
        ];
        for (a, b) in equal {
            assert_eq!(a, b);
            assert_eq!(atom_equality_hash(&a), atom_equality_hash(&b));
        }

        assert_ne!(atom_equality_hash(&Atom::sym("A")), atom_equality_hash(&Atom::sym("B")));
        assert_ne!(atom_equality_hash(&Atom::sym("A")), atom_equality_hash(&Atom::var("A")));
        assert_ne!(atom_equality_hash(&expr!("A" "B")), atom_equality_hash(&expr!(("A") "B")));
        assert_ne!(atom_equality_hash(&Atom::gnd(Number::Integer(1))), atom_equality_hash(&Atom::gnd(Number::Integer(2))));
    }

    #[test]
    fn intersection_op() {
        let intersection_op = IntersectionAtomOp{};
        let actual = intersection_op.execute(&mut vec![expr!(
                "Z"
                ("A" ("B" "C"))
                ("A" ("B" "C"))
                ("f" "g")
                ("f" "g")
                ("f" "g")
                ("P" "b")
            ), expr!(
                ("f" "g")
                ("f" "g")
                ("A" ("B" "C"))
                "p"
                "p"
                ("Q" "a")
                "Z"
            )]).unwrap();
        assert_eq_no_order!(actual, vec![expr!("Z" ("A" ("B" "C")) ("f" "g") ("f" "g"))]);

        assert_eq_no_order!(intersection_op.execute(&mut vec![expr!(
                { Number::Integer(5) }
                { Number::Integer(4) }
                { Number::Integer(3) }
                { Number::Integer(2) }
            ), expr!(
                { Number::Integer(5) }
                { Number::Integer(3) }
            )]).unwrap(), vec![expr!({Number::Integer(5)} {Number::Integer(3)})]);
    }

    #[test]
    fn subtraction_op() {
        let subtraction_op = SubtractionAtomOp{};
        let actual = subtraction_op.execute(&mut vec![expr!(
                "Z"
                "S"
                "S"
                ("A" ("B" "C"))
                ("A" ("B" "C"))
                ("f" "g")
                ("f" "g")
                ("f" "g")
                ("P" "b")
            ), expr!(
                ("f" "g")
                ("A" ("B" "C"))
                "p"
                "P"
                ("Q" "a")
                "Z"
                "S"
                "S"
                "S"
            )]).unwrap();
        assert_eq_no_order!(actual,
                   vec![expr!(("A" ("B" "C")) ("f" "g") ("f" "g") ("P" "b"))]);
    }

    #[test]
    fn intersection_and_subtraction_with_variables() {
        // Every variable used to share one wildcard key of the index, so the results
        // lost members and differed from run to run
        let lhs = expr!("A" x "B" y "C");
        let rhs = expr!(y "C" "A" x "B");
        for _ in 0..16 {
            assert_eq!(IntersectionAtomOp{}.execute(&mut vec![lhs.clone(), rhs.clone()]).unwrap(),
                vec![expr!("A" x "B" y "C")]);
            assert_eq!(SubtractionAtomOp{}.execute(&mut vec![lhs.clone(), rhs.clone()]).unwrap(),
                vec![expr!()]);
        }

        // Variables are compared by name
        assert_eq!(IntersectionAtomOp{}.execute(&mut vec![expr!(x y ("f" x)), expr!(("f" x) z x)]).unwrap(),
            vec![expr!(x ("f" x))]);
        assert_eq!(SubtractionAtomOp{}.execute(&mut vec![expr!(x y ("f" x)), expr!(("f" x) z x)]).unwrap(),
            vec![Atom::expr([Atom::var("y")])]);
    }

    #[test]
    fn intersection_and_subtraction_are_multiset_operations() {
        let lhs = expr!("a" "a" "a" "b" {Number::Integer(1)} {Number::Integer(1)});
        let rhs = expr!("a" {Number::Integer(1)} "a" "c");
        assert_eq!(IntersectionAtomOp{}.execute(&mut vec![lhs.clone(), rhs.clone()]).unwrap(),
            vec![expr!("a" "a" {Number::Integer(1)})]);
        assert_eq!(SubtractionAtomOp{}.execute(&mut vec![lhs, rhs]).unwrap(),
            vec![expr!("a" "b" {Number::Integer(1)})]);
    }

    #[test]
    fn intersection_and_subtraction_compare_atoms_by_equality() {
        // An integer is equal to the float of the same value, like in `==` and `unique-atom`
        let lhs = expr!({Number::Integer(1)} {Number::Integer(2)} {Number::Float(0.0)});
        let rhs = expr!({Number::Float(1.0)} {Number::Float(-0.0)} {Number::Integer(3)});
        assert_eq!(IntersectionAtomOp{}.execute(&mut vec![lhs.clone(), rhs.clone()]).unwrap(),
            vec![expr!({Number::Integer(1)} {Number::Float(0.0)})]);
        assert_eq!(SubtractionAtomOp{}.execute(&mut vec![lhs, rhs]).unwrap(),
            vec![Atom::expr([Atom::gnd(Number::Integer(2))])]);

        // Grounded atoms other than numbers are found as well
        let lhs = expr!({Bool(true)} {Bool(false)} {Bool(true)});
        let rhs = Atom::expr([Atom::gnd(Bool(true))]);
        assert_eq!(IntersectionAtomOp{}.execute(&mut vec![lhs.clone(), rhs.clone()]).unwrap(),
            vec![Atom::expr([Atom::gnd(Bool(true))])]);
        assert_eq!(SubtractionAtomOp{}.execute(&mut vec![lhs, rhs]).unwrap(),
            vec![expr!({Bool(false)} {Bool(true)})]);
    }

    #[test]
    fn get_type_op() {
        let space = metta_space("
            (: B Type)
            (: C Type)
            (: A B)
            (: A C)
        ");

        let get_type_op = GetTypeOp::new(space.clone());
        assert_eq_no_order!(get_type_op.execute(&mut vec![sym!("A"), expr!({space.clone()})]).unwrap(),
            vec![sym!("B"), sym!("C")]);
    }

    #[test]
    fn get_type_op_non_valid_atom() {
        let space = metta_space("
            (: f (-> Number String))
            (: 42 Number)
            (: \"test\" String)
        ");

        let get_type_op = GetTypeOp::new(space.clone());
        assert_eq_no_order!(get_type_op.execute(&mut vec![expr!("f" "42"), expr!({space.clone()})]).unwrap(),
            vec![sym!("String")]);
        assert_eq_no_order!(get_type_op.execute(&mut vec![expr!("f" "\"test\""), expr!({space.clone()})]).unwrap(),
            vec![EMPTY_SYMBOL]);
    }
}
