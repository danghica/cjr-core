"""Check offline HTML files and fragments across a repository and its dependencies."""
from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import urlsplit,unquote
import json,sys
class Info(HTMLParser):
    def __init__(self,text):super().__init__();self.ids=set();self.links=[];self.feed(text)
    def handle_starttag(self,tag,attrs):
        for key,value in attrs:
            if key in ('id','name') and value:self.ids.add(value)
            if key in ('href','src') and value:self.links.append(value)
def audit(root):
    root=Path(root).resolve();pages={p.resolve():Info(p.read_text()) for p in root.rglob('*.html') if '.git' not in p.parts}
    errors=[]
    for p,info in pages.items():
        for link in info.links:
            u=urlsplit(link)
            if u.scheme or u.netloc:continue
            target=(p.parent/unquote(u.path)).resolve() if u.path else p
            if not target.is_file():errors.append({'page':str(p.relative_to(root)),'link':link,'reason':'missing file'})
            elif u.fragment and target.suffix=='.html':
                other=pages.get(target) or Info(target.read_text())
                if unquote(u.fragment) not in other.ids:errors.append({'page':str(p.relative_to(root)),'link':link,'reason':'missing fragment'})
    return {'pages':len(pages),'errors':errors,'status':'passed' if not errors else 'failed'}
if __name__=='__main__':
    result=audit(Path(sys.argv[1]));print(json.dumps(result,indent=2));raise SystemExit(bool(result['errors']))
