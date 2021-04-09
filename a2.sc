
sealed trait STType
case object STNat extends STType {
  override def toString() = "nat"
}
case object STBool extends STType {
  override def toString() = "bool"
}
// Functions have a domain type and a codomain type.
case class STFun(dom: STType, codom: STType) extends STType {
  override def toString() = "(" + dom.toString + ") -> (" + codom.toString + ")"
}


sealed trait STTerm
case class STVar(index: Int) extends STTerm {
  override def toString() = index.toString()
}

case class STApp(t1: STTerm, t2: STTerm) extends STTerm {
  override def toString() = "(" + t1.toString() + ") (" + t2.toString() + ")"
}

case class STAbs(sttype: STType, t: STTerm) extends STTerm{
  override def toString() = "lambda . " + t.toString()
}

case object STZero extends STTerm{
  override def toString() = "zero"
}

case class STSuc(t: STTerm) extends STTerm{
  override def toString() = "suc " + t.toString
}

case class STIsZero(t: STTerm) extends STTerm{
  override def toString() = "iszero " + t.toString
}

case object STTrue extends STTerm{
  override def toString = "true"
}

case object STFalse extends STTerm{
  override def toString = "false"
}

case class STTest(t1: STTerm, t2: STTerm, t3: STTerm) extends STTerm{
  override def toString() =
    "test (" + b.toString + ") (" + t1.toString + ") (" + t2.toString + ")"
}

def emptyEnv(): Int => Option[STType] = _ => None

def prependEnv(a: STType, env: Int => Option[STType]): Int => Option[STType] = {
  i => i match {
    case 0 => Some(a)
    case n => env(n-1)
  }
}

def typeOf(t: STTerm, l: List[STType]) : Option [STType] = {
  try{
      t match{
         case STZero => Some(STNat)
         case STTrue => Some(STBool)
         case STFalse => Some(STBool)
         case STAbs(x, t) => typeOf(t, x+:l) match {
              case Some(i) => Some(STFun(x,i))
          }  
         case STIsZero(x) if (typeOf(x,l)==Some(STNat)) => Some(STBool)
         case STSuc(x) if (typeOf(x,l)==Some(STNat)) => Some(STNat)   
         case STApp(x, y) => typeOf(x,l) match {
              case Some(STFun(dom,codom)) if (typeOf(y,l)==Some(dom)) => Some(codom)

         }
         case STVar(x) if (l.length > x)=> Some(l(x))
         case STTest(x, y, z) if (typeOf(x,l)==Some(STBool) && typeOf(y,l)==typeOf(z,l))=> typeOf(y,l)      
      }
  }
  catch{
    case _ => None
  }
}


def typecheck(t: STTerm): Boolean = t match {
    case t if (typeOf(t,List())== None)=> false
    case t if (typeOf(t,List())!= None)=> true
}

  
  //---------------------------------------------------------

sealed trait ULTerm
case class ULVar(index: Int) extends ULTerm {
  override def toString() = index.toString()
}
case class ULAbs(t: ULTerm) extends ULTerm {
  override def toString() = "lambda . " + t.toString()
}
case class ULApp(t1: ULTerm, t2: ULTerm) extends ULTerm {
  override def toString() = "(" + t1.toString() + ") (" + t2.toString() + ")"
}
// Shift the numbering of unbound variables
def shift(shiftAmount: Int, t: ULTerm): ULTerm = {
  // Walk through the term and shift all variables with index
  // greater than or equal to c, which is maintained to be
  // the number of variable binders (abstractions) outside the current subterm.
  def walk(currentBinders: Int, t: ULTerm): ULTerm = t match {
    // Check if x is a free variable; that is,
    // if the number x is greater than or equal to
    // the number of variable binders encountered outside this subterm.
    case ULVar(x) if (x >= currentBinders) => ULVar(x+shiftAmount)
    case ULVar(x) => ULVar(x)

    case ULAbs(t) =>
      // We now have one more variable binder outside the subterm.
      // Increment currentBinders and walk into the subterm.
      ULAbs(walk(currentBinders+1, t))

    case ULApp(t1,t2) =>
      // No new variable binders. Just walk into the subterms.
      ULApp(walk(currentBinders,t1),walk(currentBinders,t2))
  }

  // Walk the term and perform the shift of free variables.
  // We begin with 0 variable binders outside.
  walk(0, t)
}
// In our usual syntax, we would write substitution as `t[x := r]`.
// Here we write `substitute(t,x,r)`.
def substitute(t: ULTerm, x: Int, r: ULTerm): ULTerm = {
  // We want to substitute for the free variable with number x.
  // Inside a variable binder (abstraction),
  // the index of all free variables is shifted up by 1.
  // So we must keep track of the number of binders outside the current subterm.
  def walk(currentBinders: Int, t: ULTerm): ULTerm = t match {
    case ULVar(y) if y == x + currentBinders =>
      // y is the xth free variable. Substitute for it,
      // making sure to shift the free variables in r
      // to account for the number of variable binders outside this subterm.
      shift(currentBinders,r)
    
    case ULVar(y) =>
      // Otherwise, y is not the xth free variable;
      // leave it as is.
      ULVar(y)
    
    case ULAbs(t) =>
      // We now have one more variable binder outside the subterm.
      // Increment currentBinders and walk into the subterm.
      ULAbs(walk(currentBinders+1,t))

    case ULApp(t1,t2) =>
      // No new variable binders. Just walk into the subterms.
      ULApp(walk(currentBinders,t1),walk(currentBinders,t2))
  }

  // Walk the term, performing the substitution.
  // We begin with 0 variable binders outside.
  walk(0,t)
}
// We need to know if a term is a value during reduction
// when using call-by-value semantics.
def isValue(t: ULTerm): Boolean = t match {
  case ULAbs(_) => true
  case _ => false
}
// Call-by-value reduction function.
// Performs one step of evaluation, if possible according to the call-by-value rules.
// If no reduction is possible, returns None.
def reduce(t: ULTerm): Option[ULTerm] = t match {

  // Case: the left term is an abstraction, and the right is a value.
  // Then apply the value to the abstraction.
  case ULApp(ULAbs(t),v) if isValue(v) =>
    // When we apply the value to the abstraction,
    // we must shift the value's free variables up by 1 to account
    // for the abstraction's variable binder.
    val r = substitute(t,0,shift(1,v))
    // Then, we need to shift the result back.
    // Since the abstraction's variable is now "used up".
    Some(shift(-1,r))

  // Case: the left term is a value, then try to reduce the right term.
  case ULApp(v,t) if isValue(v) =>
    reduce(t) match {
      case Some(r) => Some(ULApp(v,r))
      case None => None
    }

  // Case: the left term is not a value (not an abstraction.)
  // Try to reduce it.
  case ULApp(t1,t2) =>
    reduce(t1) match {
      case Some(r1) => Some(ULApp(r1,t2))
      case None => None
    }
    
  case _ => None
}

// Evaluation just repeatedly applies reduce,
// until we reach None (signifying reduction failed.)
def evaluate(t: ULTerm): ULTerm = reduce(t) match {
  case None => t
  case Some(r) => evaluate(r)
}

//-----------------------------------------------------------------------------------------------------------------------
  
def eraseTypes(t1: STTerm) : ULTerm = t1 match {
  case STTrue => ULAbs(ULAbs(ULVar(1)))
  case STFalse => ULAbs(ULAbs(ULVar(0)))
  case STTest(x,y,z) => ULAbs(ULAbs(ULAbs(ULApp(ULApp(eraseTypes(x),eraseTypes(y)),eraseTypes(z)))))
  case STZero => ULAbs(ULAbs(ULVar(0)))
  case STSuc(x) => ULApp(ULAbs(ULAbs(ULAbs(ULApp(ULVar(1),ULApp(ULApp(ULVar(2),ULVar(1)),ULVar(0)))))),eraseTypes(x))
  case STIsZero(x) => ULApp(ULAbs(ULApp(ULApp(ULVar(0), ULAbs(eraseTypes(STFalse))), eraseTypes(STTrue))), eraseTypes(x))
  case STApp(x,y) => ULApp(eraseTypes(x),eraseTypes(y))
  case STAbs(t,STVar(x)) => ULAbs(ULVar(x))
  }



  
  
  
  
  
  
  