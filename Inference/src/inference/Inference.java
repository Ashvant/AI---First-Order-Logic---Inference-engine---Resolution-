/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package inference;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

/**
 *
 * @author ashvant
 */
public class Inference {

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) throws FileNotFoundException, IOException {
        String filename="input.txt";
        FileReader fr = new FileReader(filename);
        BufferedReader br = new BufferedReader(fr);
        String sCurrentLine;
        int lineNumber = 0;
        int queryCount=0;
        int kbCount = 0;
        Integer number = 0;
        KB kbase = new KB();
        HashMap<String,List<Integer>> predicateMap = new HashMap<String,List<Integer>>();
        Queries queries = new Queries();
        ArrayList<String> QueryList = new ArrayList<String>();
        ArrayList<String> KBList = new ArrayList<String>();
        while ((sCurrentLine = br.readLine()) != null)
            {       
                if(lineNumber==0){
                    queryCount = Integer.parseInt(sCurrentLine);
                    
                }
                if(lineNumber>0 && lineNumber <queryCount+1 ){
                    String currentLine = sCurrentLine.replaceAll("\\s+","");
                  //  System.out.println(currentLine);
                    QueryList.add(currentLine);
                    parseQuery(currentLine,queries);
                    
                }
                if(lineNumber == queryCount+1){
                    kbCount = Integer.parseInt(sCurrentLine);
                }
                if(lineNumber>queryCount+1){
                    String currentLine = sCurrentLine.replaceAll("\\s+","");
                 //   System.out.println(currentLine);
                    KBList.add(currentLine);
                    parseSentence(currentLine,kbase,number++);
                }
                lineNumber++;
           }
       ArrayList<Boolean> outputList = new ArrayList<Boolean>();
       
       for(int j=0;j<queries.sentenceList.size();j++){
           Boolean output = resolveQueries(kbase,queries.sentenceList.get(j));
           outputList.add(output);
           
           System.out.println(output);
       }
       printResult(outputList);
       
       
    }
    
    private static void printResult(ArrayList<Boolean> outputList){
        Writer writer = null;
        try {
            writer = new BufferedWriter(new OutputStreamWriter(
                  new FileOutputStream("output.txt"), "utf-8"));
            for(int i=0;i<outputList.size();i++){
                writer.write(outputList.get(i).toString().toUpperCase());
                writer.write("\n");
            }
        } catch (IOException ex) {
          // report
        } finally {
           try {writer.close();} catch (Exception ex) {/*ignore*/}
        }
    }
    
    static boolean resolveQueries(KB kbase,Sentences querySentence){
        KB newKB = new KB();
        
       for(int i=0;i<kbase.sentenceList.size();i++){
            newKB.copytoKB(kbase.sentenceList.get(i));
        }
        Sentences negatedQuery = querySentence;
        if(negatedQuery.clauseList.get(0).isNegated){
            negatedQuery.clauseList.get(0).isNegated = false;
        }else{
            negatedQuery.clauseList.get(0).isNegated = true;
        }
        newKB.AddtoKB(negatedQuery);
        int repeat = 0;
        HashMap<String,List<Integer>> predicateMap = createPredicateMap(newKB);
        HashSet<Sentences> fullSet = new HashSet<Sentences>();
        while(true){
            repeat = 0;
            int start = 0;
            HashSet<Sentences> newSentences = new HashSet<Sentences>();
            predicateMap = createPredicateMap(newKB);
            for(int a=0;a<newKB.sentenceList.size();a++){
                Sentences sentence1 = newKB.sentenceList.get(a);
                for(int b=start+1;b<newKB.sentenceList.size();b++){
                    Sentences sentence2 = newKB.sentenceList.get(b);
                    boolean flag = false;
                    for(int c=0;c<sentence1.clauseList.size();c++){
                        if(predicateMap.get(sentence1.clauseList.get(c).predicate).contains(b)){
                            flag =true;
                        }
                    }
                    if(flag){
                        flag = false;
                        Sentences resolvent =  resolve(sentence1,sentence2);
                        if(resolvent==null){
                            return true;
                        }
                        
                     if(!resolvent.clauseList.isEmpty() && !checkRedundancy(resolvent,fullSet))   {
                         fullSet.add(resolvent);
                         repeat--;
                         newSentences.add(resolvent);
                     }
                     
                    }
                }
            }
            start = newKB.sentenceList.size()-1;
         //  System.out.println(start);
         //  System.out.println(newSentences.size());
           if(fullSet.size()>1000){
                    return false;
            }else if(repeat == 0){
                    return false;
            }
           Iterator<Sentences> it = newSentences.iterator();
            while(it.hasNext()){
                Sentences temp = it.next();
                newKB.AddtoKB(temp);
            } 
        }
    }
    static boolean checkRedundancy(Sentences resolvent,HashSet<Sentences> newSentences){
        Iterator<Sentences> it = newSentences.iterator();
            while(it.hasNext()){
                Sentences temp = it.next();
                    if(temp.clauseList.size() == resolvent.clauseList.size()){
                        for(int i=0;i<temp.clauseList.size();i++){
                        boolean x = (temp.clauseList.get(i).predicate.equals(resolvent.clauseList.get(i).predicate));
                        boolean y = (temp.clauseList.get(i).isNegated == resolvent.clauseList.get(i).isNegated);
                        boolean z = (temp.clauseList.get(i).arguments.equals(resolvent.clauseList.get(i).arguments));
                        if(x&&y&&z){
                            return true;
                        }
                    }
                }
            }
            return false;
    }
    static Sentences resolve(Sentences sentence1,Sentences sentence2){
        Sentences newSentence = new Sentences();
        for(int i=0;i<sentence1.clauseList.size();i++){
            Clauses clause1 = sentence1.clauseList.get(i);
            for(int j=0;j<sentence2.clauseList.size();j++){
                Clauses clause2 = sentence2.clauseList.get(j);
                HashMap<String,String> substitution = new HashMap<String,String>();
                if(clause1.predicate.equals(clause2.predicate)&&clause1.isNegated!=clause2.isNegated){
                    substitution = unification((List)clause1.arguments,(List)clause2.arguments,substitution);
                    if(substitution != null){
                        Sentences subSentence1 = new Sentences();
                        Sentences subSentence2 = new Sentences();
                        for(int k=0;k<sentence1.clauseList.size();k++){
                            subSentence1.AddtoSentence(sentence1.clauseList.get(k));
                        }
                        for(int k=0;k<sentence2.clauseList.size();k++){
                            subSentence2.AddtoSentence(sentence2.clauseList.get(k));
                        }
                
                        applySubstitution(substitution,subSentence1);
                        applySubstitution(substitution,subSentence2);
                        subSentence1.clauseList.remove(i);
                        subSentence2.clauseList.remove(j);
                        
                        for(int k=0;k<subSentence1.clauseList.size();k++){
                            newSentence.AddtoSentence(subSentence1.clauseList.get(k));
                        }
                        for(int k=0;k<subSentence2.clauseList.size();k++){
                            newSentence.AddtoSentence(subSentence2.clauseList.get(k));
                        }
                        if(newSentence.clauseList.isEmpty()){
                            return null;
                        }else{
                            Sentences resolvent = factorSentence(newSentence);
                            return resolvent;
                        }
                        
                    }
                }
            }
            
        }
        return newSentence;
    }
    static Sentences factorSentence(Sentences newSentence){
        for(int i=0;i<newSentence.clauseList.size();i++){
            Clauses clause1 = newSentence.clauseList.get(i);
            for(int j=i+1;j<newSentence.clauseList.size();j++){
                Clauses clause2 = newSentence.clauseList.get(j);
                HashMap<String,String> substitution = new HashMap<String,String>();
                if(clause1.predicate.equals(clause2.predicate) && clause1.isNegated == clause2.isNegated){
                    substitution = unification((List)clause1.arguments,(List)clause2.arguments,substitution);
                    if(substitution != null){
                        Sentences subSentence1 = new Sentences();
                        for(int k=0;k<newSentence.clauseList.size();k++){
                            subSentence1.AddtoSentence(newSentence.clauseList.get(k));
                        }
                        applySubstitution(substitution,subSentence1);
                        subSentence1.clauseList.remove(i);
                        return subSentence1;
                    }
                }
            }
        }
        return newSentence;
    }
    
    static void applySubstitution(HashMap<String,String> substitution,Sentences sentence1){
        for(int i=0;i<sentence1.clauseList.size();i++){
            Clauses clause1 = sentence1.clauseList.get(i);
            for(int j=0;j<clause1.arguments.size();j++){
                if(substitution.containsKey(clause1.arguments.get(j))){
                    sentence1.clauseList.get(i).arguments.set(j, substitution.get(clause1.arguments.get(j)));
                }
            }
        }
    }
    static HashMap<String,String> unification(List<String> arg1,List<String> arg2,HashMap<String,String> substitution){
        if(substitution == null){
            return null;
        }else if(arg1.size()!=arg2.size()){
            return null;
        }else if(arg1.isEmpty() && arg2.isEmpty()){
            return substitution;
        }else if(arg1.size() ==1 && arg2.size()==1){
            return unification(arg1.get(0),arg2.get(0),substitution);
        }else{
            return unification(arg1.subList(1,arg1.size()),arg2.subList(1, arg2.size()),unification(arg1.get(0),arg2.get(0),substitution));
        }
    }
    
    static HashMap<String,String> unification(String arg1,String arg2,HashMap<String,String> substitution){
        if(substitution == null){
            return null;
        }else if(arg1.equals(arg2)){
            return substitution;
        }else if(isVariable(arg1)){
            return unificationVariables(arg1,arg2,substitution);
        }else if(isVariable(arg2)){
            return unificationVariables(arg2,arg1,substitution);
        }else{
            return null;
        }
    }
    static HashMap<String,String> unificationVariables(String arg1,String arg2,HashMap<String,String> substitution){
        if(substitution.containsKey(arg1)){
            return unification(substitution.get(arg1),arg2,substitution);
        }else if(substitution.containsKey(arg2)){
            return unification(arg1,substitution.get(arg2),substitution);
        }else{
            HashMap<String,String> theta = new HashMap<String,String>();
            theta = deepCopy(substitution);
            theta.put(arg1, arg2);
            return theta;
        }
    }
    public static HashMap<String,String> deepCopy(HashMap<String,String> original){

    HashMap<String,String> copy = new HashMap<String,String>();
    for(Entry<String,String> entry : original.entrySet()){
        copy.put(entry.getKey(),entry.getValue());
    }
    return copy;
}
    static boolean isVariable(String arg1){
        if(arg1.charAt(0)>=65 && arg1.charAt(0)<=90){
            return false;
        }else{
            return true;
        }
    }
    static HashMap<String,List<Integer>> createPredicateMap(KB kbase){
        HashMap<String,List<Integer>> predicateMap = new HashMap<String,List<Integer>>();
        for(int i=0;i<kbase.sentenceList.size();i++){
            for(int j=0;j<kbase.sentenceList.get(i).clauseList.size();j++){
                if(predicateMap.get(kbase.sentenceList.get(i).clauseList.get(j).predicate)!=null){
                    predicateMap.get(kbase.sentenceList.get(i).clauseList.get(j).predicate).add(i);
                }else{
                    ArrayList<Integer> list = new ArrayList<Integer>();
                    list.add(i);
                    predicateMap.put(kbase.sentenceList.get(i).clauseList.get(j).predicate,list);
                }
            }
        }
        
        /*Set<String> hset = predicateMap.keySet();
        Iterator<String> it = hset.iterator();
        while(it.hasNext()){
            String temp = it.next();
            System.out.println(temp);
            System.out.println(predicateMap.get(temp));
        }*/
        return predicateMap;
    }
    
    static void parseSentence(String sentence,KB kbase,Integer number){
        Sentences sent = new Sentences();
        String[] clauses  = sentence.split("\\|");
        int i=0;
        boolean isNegative;
        while(i<clauses.length){
            if(clauses[i].charAt(0)=='~'){
                isNegative = true;
                String remaining = clauses[i].substring(1);
                String[] predicateSplit = remaining.split("\\(");
                String predicate = predicateSplit[0];
                remaining = predicateSplit[1].replaceAll("\\)","");
                String[] arguments = remaining.split("\\,");
                ArrayList<String> argList = new ArrayList<String>();
                int j=0;
                while(j<arguments.length){
                    if(isVariable(arguments[j])){
                        argList.add(arguments[j]+number.toString());
                    }else{
                        argList.add(arguments[j]);
                    }
                    j++;
                }
                i++;
                Clauses clause = new Clauses(predicate,argList,isNegative);
                sent.AddtoSentence(clause);
            } else {
                isNegative = false;
                String remaining = clauses[i].substring(0);
                String[] predicateSplit = remaining.split("\\(");
                String predicate = predicateSplit[0];
                remaining = predicateSplit[1].replaceAll("\\)","");
                String[] arguments = remaining.split("\\,");
                ArrayList<String> argList = new ArrayList<String>();
                int j=0;
                while(j<arguments.length){
                   if(isVariable(arguments[j])){
                        argList.add(arguments[j]+number.toString());
                    }else{
                        argList.add(arguments[j]);
                    }
                    j++;
                }
                i++;
                Clauses clause = new Clauses(predicate,argList,isNegative);
                sent.AddtoSentence(clause);
            }
        }
        kbase.AddtoKB(sent);
    }
    static void parseQuery(String sentence,Queries queries){
        Sentences sent = new Sentences();
        String[] clauses  = sentence.split("\\|");
        int i=0;
        boolean isNegative;
        while(i<clauses.length){
            if(clauses[i].charAt(0)=='~'){
                isNegative = true;
                String remaining = clauses[i].substring(1);
                String[] predicateSplit = remaining.split("\\(");
                String predicate = predicateSplit[0];
                remaining = predicateSplit[1].replaceAll("\\)","");
                String[] arguments = remaining.split("\\,");
                ArrayList<String> argList = new ArrayList<String>();
                int j=0;
                while(j<arguments.length){
                    argList.add(arguments[j]);
                    j++;
                }
                i++;
                Clauses clause = new Clauses(predicate,argList,isNegative);
                sent.AddtoSentence(clause);
            } else {
                isNegative = false;
                String remaining = clauses[i].substring(0);
                String[] predicateSplit = remaining.split("\\(");
                String predicate = predicateSplit[0];
                remaining = predicateSplit[1].replaceAll("\\)","");
                String[] arguments = remaining.split("\\,");
                ArrayList<String> argList = new ArrayList<String>();
                int j=0;
                while(j<arguments.length){
                    argList.add(arguments[j]);
                    j++;
                }
                i++;
                Clauses clause = new Clauses(predicate,argList,isNegative);
                sent.AddtoSentence(clause);
            }
        }
        queries.AddtoKB(sent);
    }
}
class KB{
    ArrayList<Sentences> sentenceList = new ArrayList<Sentences>();
    void AddtoKB(Sentences Sentence){
        sentenceList.add(Sentence);
    }
    void copytoKB(Sentences Sentence){
        Sentences sentence = new Sentences();
        for(int i=0;i<Sentence.clauseList.size();i++){
           // Clauses cobj = new Clauses(Sentence.clauseList.get(i).predicate,Sentence.clauseList.get(i).arguments,Sentence.clauseList.get(i).isNegated);
            sentence.AddtoSentence(Sentence.clauseList.get(i));
        }
        AddtoKB(sentence);
    }
}

class Sentences{
    ArrayList<Clauses> clauseList;
    Sentences(){
        clauseList = new ArrayList<Clauses>();
    }
    void AddtoSentence(Clauses clause){
        Clauses cobj = new Clauses(clause.predicate,clause.arguments,clause.isNegated);
        clauseList.add(cobj);
    }
}

class Clauses{
    String predicate = null;
    ArrayList<String> arguments  = new ArrayList<String>();
    boolean isNegated = false;
    Clauses(){
        String predicate = null;
        ArrayList<String> arguments  = new ArrayList<String>();
        boolean isNegated = false;
    }
    Clauses(String thispredicate,ArrayList<String> thisarguments,boolean thisisNegated){
        predicate = thispredicate;
        for(int i=0;i<thisarguments.size();i++){
            String a = thisarguments.get(i);
            arguments.add(a);
        }
        
        isNegated = thisisNegated;
    }
}

class Queries{
    ArrayList<Sentences> sentenceList = new ArrayList<Sentences>();
    void AddtoKB(Sentences Sentence){
        sentenceList.add(Sentence);
    }
}