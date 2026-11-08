// External, reviewed adapter to the hash-pinned Alloy distribution; no proof claim.
import com.google.gson.*;
import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.*;
import edu.mit.csail.sdg.translator.*;
import kodkod.engine.satlab.SATFactory;
import java.nio.file.*;
import java.util.*;

public final class AlloyBridge {
    static final class Unsupported extends RuntimeException {
        Unsupported(String reason) { super(reason); }
    }
    static final Gson JSON = new GsonBuilder().serializeNulls().create();
    static final Map<String,Object> out = new TreeMap<>();
    static void stage(String name) throws Exception {
        out.put("stage",name);
        Files.writeString(Path.of("execution.json"),JSON.toJson(out));
    }
    static void require(boolean ok, String why) {
        if (!ok) throw new IllegalArgumentException(why);
    }
    static void supported(boolean ok, String why) { if(!ok) throw new Unsupported(why); }
    static String uid(String name) {
        supported(name.startsWith("this/"), "unclassified module symbol: " + name);
        return name.substring(5);
    }
    static Map<String,Object> command(Command c) {
        Map<String,Object> m = new TreeMap<>();
        m.put("label", c.label); m.put("check", c.check); m.put("overall", c.overall);
        m.put("bitwidth", c.bitwidth); m.put("maxseq", c.maxseq);
        m.put("minprefix", c.minprefix); m.put("maxprefix", c.maxprefix);
        m.put("maxstring", c.maxstring); m.put("expects", c.expects);
        List<Object> scopes = new ArrayList<>();
        for (CommandScope s : c.scope) scopes.add(Map.of("uid", uid(s.sig.label),
            "exact", s.isExact, "start", s.startingScope, "end", s.endingScope, "increment", s.increment));
        m.put("scopes", scopes); m.put("formula", c.formula.toString());
        m.put("additional_exact_scopes", c.additionalExactScopes.stream().map(s -> s.label).toList());
        return m;
    }
    // The importer validates the complete original generated grammar. This
    // second check inspects the resolved facts/pin and forbids hidden arithmetic.
    static void audit(Expr e, Set<Expr> seen, Set<String> users, long maximum) throws Err {
        if (!seen.add(e)) return;
        require(e.type().arity() <= 2, "arity exceeds range argument");
        if (e instanceof ExprBinary x) {
            require(Set.of("ARROW", "JOIN", "PLUS", "INTERSECT", "MINUS", "EQUALS", "NOT_EQUALS",
                "IN", "NOT_IN", "AND", "OR", "IMPLIES", "IFF", "LTE", "GTE", "LT", "GT").contains(x.op.name()),
                "unsupported binary arithmetic/operator: " + x.op.name());
            audit(x.left, seen, users, maximum); audit(x.right, seen, users, maximum);
        } else if (e instanceof ExprUnary x) {
            require(Set.of("NOOP", "NOT", "NO", "SOME", "ONE", "LONE", "CARDINALITY", "SETOF", "ONEOF",
                "LONEOF", "SOMEOF", "TRANSPOSE", "CAST2INT").contains(x.op.name()), "unsupported unary: " + x.op.name());
            audit(x.sub, seen, users, maximum);
        } else if (e instanceof ExprQt x) {
            require(Set.of("ALL", "SOME", "NO", "ONE", "LONE").contains(x.op.name()), "unsupported quantifier");
            for (Decl d : x.decls) audit(d.expr, seen, users, maximum);
            audit(x.sub, seen, users, maximum);
        } else if (e instanceof ExprList x) {
            require(Set.of("AND", "OR", "DISJOINT").contains(x.op.name()), "unsupported list operator");
            for (Expr a : x.args) audit(a, seen, users, maximum);
        } else if (e instanceof ExprLet x) {
            audit(x.expr, seen, users, maximum); audit(x.sub, seen, users, maximum);
        } else if (e instanceof ExprCall x) {
            require(Set.of("this/show", "this/ib_candidate").contains(x.fun.label) && x.args.isEmpty(),
                "unsupported call: " + x.fun.label);
            audit(x.fun.getBody(), seen, users, maximum);
        } else if (e instanceof ExprConstant x) {
            require(Set.of("TRUE", "FALSE", "EMPTYNESS", "NUMBER").contains(x.op.name()), "unsupported constant");
            if (x.op.name().equals("NUMBER")) require(Math.abs((long)x.num) <= maximum, "literal range");
        } else if (e instanceof Sig x) {
            require(x == Sig.NONE || users.contains(x.label), "non-user relation in cardinality domain: " + x.label);
        } else if (e instanceof Sig.Field || e instanceof ExprVar) {
            // Fields were checked against receipt inventory; variables bound above.
        } else throw new IllegalArgumentException("unsupported expression: " + e.getClass().getName());
    }
    static List<List<String>> tuples(A4TupleSet ts) {
        List<List<String>> rows = new ArrayList<>();
        for (A4Tuple t : ts) {
            List<String> row = new ArrayList<>();
            for (int i=0; i<t.arity(); i++) row.add(t.atom(i));
            rows.add(row);
        }
        rows.sort(Comparator.comparing(Object::toString));
        return rows;
    }
    static Map<String,Object> execute(JsonObject r) throws Exception {
        require(Runtime.version().feature() == 17, "Java 17 required");
        out.put("java",Map.of("runtime",System.getProperty("java.runtime.version"), "vendor",System.getProperty("java.vendor"),
            "vm",System.getProperty("java.vm.name"), "vm_version",System.getProperty("java.vm.version")));
        A4Reporter reporter = new A4Reporter();
        stage("original_parse");
        CompModule original = CompUtil.parseEverything_fromFile(reporter, null, "original.als");
        stage("original_command_validation");
        require(original.getAllCommands().size() == 1, "original command count");
        Command oc = original.getAllCommands().get(0);
        require(oc.label.equals("show") && !oc.check && oc.overall == 1 &&
            oc.bitwidth == -1 && oc.additionalExactScopes.isEmpty(), "original command changed");
        JsonObject originalScopes = r.getAsJsonObject("original_scopes");
        require(oc.scope.size() == originalScopes.size(), "original scope count");
        Set<String> originalScoped = new HashSet<>();
        for (CommandScope s : oc.scope) {
            String u = uid(s.sig.label);
            require(originalScopes.has(u) && originalScoped.add(u) && !s.isExact &&
                s.startingScope == originalScopes.get(u).getAsInt() &&
                s.endingScope == s.startingScope && s.increment == 1, "original scope mismatch: " + u);
        }
        out.put("original_command",command(oc));
        stage("comparison_parse");
        CompModule model = CompUtil.parseEverything_fromFile(reporter, null, "comparison.als");
        stage("profile_validation");
        require(model.getAllCommands().size() == 1, "comparison command count");
        Command c = model.getAllCommands().get(0);
        require(!CompUtil.isTemporalModel(model.getAllReachableSigs(), c), "temporal model");
        require(!c.check && c.label.equals(r.get("command").getAsString()) &&
            c.overall == r.get("overall").getAsInt() && c.bitwidth == r.get("bitwidth").getAsInt() &&
            c.maxseq == 0 && c.additionalExactScopes.isEmpty(), "comparison command mismatch");
        JsonObject expected = r.getAsJsonObject("bounds"), fieldSpec = r.getAsJsonObject("fields");
        require(c.scope.size() == expected.size(), "scope count");
        Set<String> scoped = new HashSet<>();
        for (CommandScope s : c.scope) {
            String u = uid(s.sig.label);
            require(expected.has(u) && scoped.add(u) && !s.isExact && s.startingScope == expected.get(u).getAsInt() &&
                s.endingScope == s.startingScope && s.increment == 1, "scope mismatch: " + u);
        }
        Map<String,Sig> signatures = new TreeMap<>();
        Map<String,Sig.Field> fields = new TreeMap<>();
        List<String> auxiliaries = new ArrayList<>();
        for (Sig s : model.getAllReachableSigs()) {
            if (s.builtin) {
                supported(Set.of("univ", "Int", "seq/Int", "String", "none").contains(s.label) && s.getFields().isEmpty(),
                    "unclassified built-in: " + s.label);
                auxiliaries.add(s.label); continue;
            }
            String u = uid(s.label);
            supported(expected.has(u),"unclassified auxiliary signature: " + u);
            require(expected.has(u) && signatures.put(u,s) == null && s instanceof Sig.PrimSig &&
                s.isVariable == null && s.isSubset == null, "unclassified signature: " + u);
            JsonObject node = r.getAsJsonObject("nodes").getAsJsonObject(u);
            String parent = ((Sig.PrimSig)s).parent == Sig.UNIV ? "" : uid(((Sig.PrimSig)s).parent.label);
            require(parent.equals(node.get("super").isJsonNull() ? "" : node.get("super").getAsString()) &&
                (s.isAbstract != null) == node.get("abstract").getAsBoolean(), "signature hierarchy");
            for (Sig.Field f : s.getFields()) {
                supported(fieldSpec.has(f.label),"unclassified auxiliary field: " + f.label);
                require(fieldSpec.has(f.label) && fields.put(f.label, f) == null && f.type().arity()==2 &&
                    f.isVariable == null && !f.defined, "unclassified field: " + f.label);
                JsonObject spec = fieldSpec.getAsJsonObject(f.label);
                require(spec.get("owner").getAsString().equals(u), "field owner");
                // Type.fold() can widen a declared child endpoint to its abstract
                // parent. Check the resolved declaration, preserving its identity.
                Expr target = f.decl().expr;
                while (target instanceof ExprUnary x && Set.of("NOOP","SETOF","ONEOF","LONEOF","SOMEOF").contains(x.op.name()))
                    target = x.sub;
                require(target instanceof Sig && uid(((Sig)target).label).equals(spec.get("target").getAsString()), "field target");
            }
        }
        require(signatures.size() == expected.size() && fields.size() == fieldSpec.size(), "declaration inventory");
        Set<String> labels = new HashSet<>(); for(Sig s:signatures.values()) labels.add(s.label);
        Set<Expr> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        long maximum = r.get("maximum").getAsLong();
        audit(c.formula, seen, labels, maximum);
        audit(model.getAllReachableFacts(), seen, labels, maximum);
        for(Sig s:signatures.values()) for(Expr fact:s.getFacts()) audit(fact, seen, labels, maximum);
        A4Options options = new A4Options();
        options.solver = SATFactory.get("sat4j");
        require(options.solver.id().equals("sat4j") && !options.solver.unbounded() && options.solver.isPresent(), "SAT4J unavailable");
        options.symmetry=0; options.skolemDepth=0; options.inferPartialInstance=false;
        options.noOverflow=true; options.unrolls=-1; options.coreMinimization=2;
        options.coreGranularity=0; options.recordKodkod=false;
        options.decompose_mode=0; options.decompose_threads=1;
        options.originalFilename="comparison.als"; options.tempDirectory="."; options.solverDirectory="";
        Map<String,Object> effective = new TreeMap<>();
        for(java.lang.reflect.Field f:A4Options.class.getFields())
            if(!java.lang.reflect.Modifier.isStatic(f.getModifiers()))
                effective.put(f.getName(), f.getName().equals("solver") ? options.solver.id() : f.get(options));
        out.put("command",command(c)); out.put("options",effective); out.put("auxiliaries",auxiliaries);
        // Retain effective options and checked AST even if execution is interrupted.
        stage("solver");
        A4Solution solution = TranslateAlloyToKodkod.execute_command(reporter, model.getAllReachableSigs(), c, options);
        out.put("outcome",solution.satisfiable() ? "sat" : "unsat");
        stage("witness");
        // Alloy 6.2 wraps even static SAT results in a one-state TemporalInstance
        // (A4Solution.java:1668). Check the model and effective search bounds.
        require(solution.getMinTrace() == -1 && solution.getMaxTrace() == -1, "temporal search bounds");
        out.put("static_trace", Map.of("min",solution.getMinTrace(),"max",solution.getMaxTrace()));
        if (solution.satisfiable()) {
            Map<String,Object> extents=new TreeMap<>(), relations=new TreeMap<>();
            for(var entry:signatures.entrySet()) {
                List<List<String>> rows=tuples(solution.eval(entry.getValue()));
                require(rows.size() <= expected.get(entry.getKey()).getAsInt(),"witness exceeds scope");
                extents.put(entry.getKey(),rows.stream().map(row->row.get(0)).toList());
            }
            for(var entry:fields.entrySet()) relations.put(entry.getKey(),tuples(solution.eval(entry.getValue())));
            // Skolems are compiler-generated witnesses for the quantified pin.
            // They introduce no atoms/fields; record all of them for inspection.
            Map<String,Object> skolems=new TreeMap<>();
            for(ExprVar sk:solution.getAllSkolems()) {
                supported(sk.label.startsWith("$" + r.get("command").getAsString() + "_ib_obj_"),"unclassified skolem: " + sk.label);
                skolems.put(sk.label,tuples((A4TupleSet)solution.eval(sk)));
            }
            require(solution.eval(Sig.STRING).size()==0 && solution.eval(Sig.SEQIDX).size()==0,"unexpected auxiliary atoms");
            out.put("witness",Map.of("signatures",extents,"fields",relations,"skolems",skolems));
            solution.writeXML("witness.xml", Collections.emptyList());
        }
        out.put("status","ok");
        stage("complete");
        return out;
    }
    public static void main(String[] args) throws Exception {
        out.put("schema","clafer-alloy-bridge/1"); out.put("outcome",null); out.put("stage","request");
        try { execute(JsonParser.parseString(Files.readString(Path.of("request.json"))).getAsJsonObject()); }
        catch(Unsupported error) { out.put("status","unsupported"); out.put("detail",error.toString()); }
        catch(OutOfMemoryError error) { out.put("status","resource_limit"); out.put("detail",error.toString()); }
        catch(Throwable error) { error.printStackTrace(System.err); out.put("status","error"); out.put("detail",error.toString()); }
        Files.writeString(Path.of("solver.json"),JSON.toJson(out));
    }
}
